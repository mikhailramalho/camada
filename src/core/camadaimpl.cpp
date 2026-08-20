/**************************************************************************
 *
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *
 **************************************************************************/

#include "camadaimpl.h"
#include "../camadaerrors.h"
#include "../theories/camadatuple.h"

#include <algorithm>
#include <cstdio>
#include <limits>
#include <memory>
#include <mutex>

namespace camada {

// ---------------------------------------------------------------------------
// Wrapper-definition macros.
//
// Every public entry point in this file is a precondition check, a call into
// the backend override or the common-layer default, and a postcondition on
// the result. These macros hold the shapes that recur, so the checks cannot
// drift apart between operations that ought to share them.
// ---------------------------------------------------------------------------

#define CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(ReturnType, Name, SortAssert,      \
                                            ImplCall, ResultAssert)            \
  ReturnType SMTSolverImpl::Name(const SMTExprRef &LHS,                        \
                                 const SMTExprRef &RHS) {                      \
    SortAssert;                                                                \
    SMTExprRef theExp = ImplCall;                                              \
    ResultAssert;                                                              \
    return theExp;                                                             \
  }
#define CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(ReturnType, Name, SortAssert,       \
                                           ImplCall, ResultAssert)             \
  ReturnType SMTSolverImpl::Name(const SMTExprRef &Exp) {                      \
    SortAssert;                                                                \
    SMTExprRef theExp = ImplCall;                                              \
    ResultAssert;                                                              \
    return theExp;                                                             \
  }
// Floating-point operations dispatch on the operand's encoding: a BV-encoded
// sort must go to the common layer's bit-blast, because the backend override
// only understands its own native FP sort. Writing that ternary by hand at
// every operation is how a backend ends up being handed a sort it cannot
// represent, so the dispatch lives here instead.
#define CAMADA_DEFINE_FP_UNARY_WRAPPER(Name, ImplName, SortAssert,             \
                                       ResultAssert)                           \
  SMTExprRef SMTSolverImpl::Name(const SMTExprRef &Exp) {                      \
    SortAssert;                                                                \
    SMTExprRef theExp =                                                        \
        usesBVFPEncoding(Exp) ? SMTSolverImpl::ImplName(Exp) : ImplName(Exp);  \
    ResultAssert;                                                              \
    return theExp;                                                             \
  }
// Default *Impl for an operation a backend need not provide natively: build it
// from operations that already exist, then rewrap so the result still reports
// its own kind rather than the kind of whatever it was composed from. The
// rewrap is the part that is easy to forget when writing these by hand.
#define CAMADA_DEFINE_DERIVED_BINARY_IMPL(Name, Composition, Kind)             \
  SMTExprRef SMTSolverImpl::Name(const SMTExprRef &LHS,                        \
                                 const SMTExprRef &RHS) {                      \
    SMTExprRef theExp = Composition;                                           \
    return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::Kind);           \
  }
// Default *Impl for a feature a backend does not implement: abort with the
// theory's name. Variadic so one macro covers every parameter shape, and the
// parameters stay unnamed because nothing reads them.
#define CAMADA_DEFINE_UNSUPPORTED_IMPL(ReturnType, Name, Feature, ...)         \
  ReturnType SMTSolverImpl::Name(__VA_ARGS__) { unsupportedFeature(Feature); }
// Width-extension wrapper: same guard and postcondition for sign- and
// zero-extension. The guard is what stops i + width wrapping unsigned, so it
// belongs with the operation rather than being retyped per extension.
#define CAMADA_DEFINE_BV_EXTEND_WRAPPER(Name, ImplName, What)                  \
  SMTExprRef SMTSolverImpl::Name(unsigned i, const SMTExprRef &Exp) {          \
    requireBVSort(Exp, "Expected bit-vector expression");                      \
    fatalErrorIf(i > std::numeric_limits<unsigned>::max() - Exp->getWidth(),   \
                 "Bit-vector " What " extension width overflow");              \
    SMTExprRef theExp = ImplName(i, Exp);                                      \
    assert(theExp->getWidth() == Exp->getWidth() + i);                         \
    return theExp;                                                             \
  }
// FP arithmetic taking a rounding mode: same encoding dispatch as the unary
// FP wrapper, same postcondition that the result keeps the operand's sort.
#define CAMADA_DEFINE_FP_RM_BINARY_WRAPPER(Name, ImplName)                     \
  SMTExprRef SMTSolverImpl::Name(const SMTExprRef &LHS, const SMTExprRef &RHS, \
                                 const SMTExprRef &R) {                        \
    requireFPSameSortAndRM(LHS, RHS, R);                                       \
    SMTExprRef theExp = usesBVFPEncoding(LHS)                                  \
                            ? SMTSolverImpl::ImplName(LHS, RHS, R)             \
                            : ImplName(LHS, RHS, R);                           \
    assert(theExp->Sort == LHS->Sort);                                         \
    return theExp;                                                             \
  }
// FP to bit-vector conversion: the width check and the postcondition tying
// the result width to ToWidth are the same for signed and unsigned.
#define CAMADA_DEFINE_FP_TO_BV_WRAPPER(Name, ImplName)                         \
  SMTExprRef SMTSolverImpl::Name(const SMTExprRef &From, unsigned ToWidth) {   \
    requireFPSort(From, "Expected floating-point expression");                 \
    fatalErrorIf(ToWidth == 0, "Bit-vector target width must be non-zero");    \
    SMTExprRef theExp = usesBVFPEncoding(From)                                 \
                            ? SMTSolverImpl::ImplName(From, ToWidth)           \
                            : ImplName(From, ToWidth);                         \
    assert(theExp->getWidth() == ToWidth);                                     \
    return theExp;                                                             \
  }
// Model-value getter: check the sort, then delegate. The guard is the whole
// wrapper, so it is the only thing worth not retyping.
#define CAMADA_DEFINE_MODEL_GETTER(ResultType, Name, SortAssert, ImplName)     \
  SMTResult<ResultType> SMTSolverImpl::Name(const SMTExprRef &Exp) {           \
    SortAssert;                                                                \
    return ImplName(Exp);                                                      \
  }
// Constant constructor: nothing to check on the way in -- there is no operand
// -- so the wrapper is the impl call plus the postcondition on the result.
// Params and Args are passed as parenthesised lists so commas inside them do
// not split the macro's own arguments.
#define CAMADA_DEFINE_CONST_CTOR(Name, Params, Args, ResultAssert)             \
  SMTExprRef SMTSolverImpl::Name Params {                                      \
    SMTExprRef theExp = Name##Impl Args;                                       \
    ResultAssert;                                                              \
    return theExp;                                                             \
  }
// The no-argument dump entry points all render into a string through their
// own string overload and write it to stderr.
#define CAMADA_DEFINE_DUMP_TO_STDERR(Name)                                     \
  void SMTSolverImpl::Name() {                                                 \
    std::string Out;                                                           \
    Name(Out);                                                                 \
    std::fprintf(stderr, "%s", Out.c_str());                                   \
  }
// Cached nullary sort: build once, keep it on the solver. The cache field and
// the sort predicate are all that differ between them.
#define CAMADA_DEFINE_CACHED_SORT(Name, CacheField, SortPredicate)             \
  SMTSortRef SMTSolverImpl::Name() {                                           \
    if (CacheField)                                                            \
      return CacheField;                                                       \
                                                                               \
    SMTSortRef theSort = Name##Impl();                                         \
    assert(theSort->SortPredicate());                                          \
    CacheField = theSort;                                                      \
    return theSort;                                                            \
  }
// FP special value at an explicit format: the significand check, the sort
// construction that validates the format, the encoding dispatch, and all
// three postconditions are shared.
#define CAMADA_DEFINE_FP_SPECIAL_VALUE(Name, ImplName)                         \
  SMTExprRef SMTSolverImpl::Name(const bool Sgn, const unsigned ExpWidth,      \
                                 const unsigned SigWidth,                      \
                                 FPEncoding Encoding) {                        \
    fatalErrorIf(SigWidth == 0,                                                \
                 "Floating-point significand width must be non-zero");         \
    SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, Encoding);              \
    SMTExprRef theExp = usesBVFPEncoding(Sort)                                 \
                            ? SMTSolverImpl::ImplName(Sgn, ExpWidth, SigWidth) \
                            : ImplName(Sgn, ExpWidth, SigWidth);               \
    assert(theExp->isFPSort());                                                \
    assert(theExp->getWidth() == (ExpWidth + SigWidth));                       \
    assert(theExp->getWidth() == theExp->Sort->getWidthFromSolver());          \
    return theExp;                                                             \
  }

SMTHandleState *makeProcessLifetimeHandleState() {
  // The registry itself is a deliberately immortal heap allocation: states
  // must stay readable for the whole process (a handle can outlive its
  // solver, and even static-storage solvers bump their state's generation
  // during exit teardown, after any static registry would already be
  // destroyed). It stays reachable through this static pointer, so leak
  // checkers classify it as still-reachable rather than lost.
  static std::mutex RegistryMutex;
  static auto *Registry = new std::vector<std::unique_ptr<SMTHandleState>>();
  std::lock_guard<std::mutex> Lock(RegistryMutex);
  Registry->push_back(std::make_unique<SMTHandleState>());
  return Registry->back().get();
}

namespace {

std::string power2Dec(unsigned int N) {
  std::vector<unsigned char> Digits{1};
  for (unsigned int I = 0; I < N; ++I) {
    int Carry = 0;
    for (auto &Digit : Digits) {
      int Value = Digit * 2 + Carry;
      Digit = static_cast<unsigned char>(Value % 10);
      Carry = Value / 10;
    }
    while (Carry != 0) {
      Digits.push_back(static_cast<unsigned char>(Carry % 10));
      Carry /= 10;
    }
  }
  std::string Result;
  Result.reserve(Digits.size());
  for (auto It = Digits.rbegin(); It != Digits.rend(); ++It)
    Result.push_back(static_cast<char>('0' + *It));
  return Result;
}

std::string addLeadingZeroes(const std::string &Str, const unsigned Width) {
  if (Str.length() == Width)
    return Str;
  return std::string(Width - Str.length(), '0') + Str;
}

static bool usesBVFPEncoding(const SMTSortRef &Sort) {
  return Sort->isBVFPSort();
}

constexpr std::size_t fpEncodingIndex(FPEncoding Encoding) {
  return Encoding == FPEncoding::BV ? 1u : 0u;
}

constexpr std::size_t cachedSmallBVExprIndex(int64_t Value) {
  return static_cast<std::size_t>(Value + 1);
}

static bool isBinaryLiteral(const std::string &Value) {
  for (char C : Value) {
    if (C != '0' && C != '1')
      return false;
  }
  return true;
}

static bool usesBVFPEncoding(const SMTExprRef &Exp) {
  return usesBVFPEncoding(Exp->Sort);
}

static bool usesBVRMEncoding(const SMTSortRef &Sort) {
  return Sort->isBVRMSort();
}

static bool usesBVRMEncoding(const SMTExprRef &Exp) {
  return usesBVRMEncoding(Exp->Sort);
}

static void requireSameSort(const SMTExprRef &LHS, const SMTExprRef &RHS,
                            const char *Message) {
  fatalErrorIf(LHS->Sort != RHS->Sort, Message);
}

static void requireBVSort(const SMTExprRef &Exp, const char *Message) {
  fatalErrorIf(!Exp->isBVSort(), Message);
}

static void requireBVSameSort(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  requireBVSort(LHS, "Expected bit-vector expression");
  requireSameSort(LHS, RHS, "Expected bit-vector expressions with same sort");
}

static void requireBoolSort(const SMTExprRef &Exp, const char *Message) {
  fatalErrorIf(!Exp->isBoolSort(), Message);
}

static void requireBoolSameSort(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  requireBoolSort(LHS, "Expected boolean expression");
  requireSameSort(LHS, RHS, "Expected boolean expressions with same sort");
}

static void requireArithSort(const SMTExprRef &Exp, const char *Message) {
  fatalErrorIf(!Exp->isArithSort(), Message);
}

static void requireArithSameSort(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  requireArithSort(LHS, "Expected arithmetic expression");
  requireSameSort(LHS, RHS, "Expected arithmetic expressions with same sort");
}

static void requireIntSort(const SMTExprRef &Exp, const char *Message) {
  fatalErrorIf(!Exp->isIntSort(), Message);
}

static void requireIntSameSort(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  requireIntSort(LHS, "Expected integer expression");
  requireSameSort(LHS, RHS, "Expected integer expressions with same sort");
}

static void requireFPSort(const SMTExprRef &Exp, const char *Message) {
  fatalErrorIf(!Exp->isFPSort(), Message);
}

static void requireFPSort(const SMTSortRef &Sort, const char *Message) {
  fatalErrorIf(!Sort->isFPSort(), Message);
}

static void requireFPSameSort(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  requireFPSort(LHS, "Expected floating-point expression");
  requireSameSort(LHS, RHS,
                  "Expected floating-point expressions with same sort");
}

static void requireRMSort(const SMTExprRef &Exp, const char *Message) {
  fatalErrorIf(!Exp->isRMSort(), Message);
}

static void requireMatchingFPAndRMEncoding(const SMTExprRef &FP,
                                           const SMTExprRef &RM) {
  requireRMSort(RM, "Expected rounding-mode expression");
  fatalErrorIf(
      usesBVFPEncoding(FP) != usesBVRMEncoding(RM),
      "Floating-point expression and rounding mode use different encodings");
}

static void requireFPSameSortAndRM(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const SMTExprRef &RM) {
  requireFPSameSort(LHS, RHS);
  requireMatchingFPAndRMEncoding(LHS, RM);
}

} // namespace

SMTExprRef SMTSolverImpl::getBVZero1Expr() const {
  return CachedSmallBVZeroExprs[1];
}

SMTExprRef SMTSolverImpl::getBVOne1Expr() const { return CachedBVOne1Expr; }

SMTExprRef SMTSolverImpl::getBVZero2Expr() const {
  return CachedSmallBVZeroExprs[2];
}

SMTExprRef SMTSolverImpl::getBVZero3Expr() const {
  return CachedSmallBVZeroExprs[3];
}

SMTExprRef SMTSolverImpl::getBVZero4Expr() const {
  return CachedSmallBVZeroExprs[4];
}

SMTExprRef SMTSolverImpl::getRMExpr(RM R) const {
  return CachedRMBVExprs[static_cast<std::size_t>(R)];
}

void SMTSolverImpl::invalidateGeneratedObjects() {
  clearSortCaches();
  clearExprCaches();
  HandleState->bumpGeneration();
  ExprArena.clear();
  SortArena.clear();
}

void SMTSolverImpl::clearSortCaches() {
  CachedBoolSort = {};
  CachedIntSort = {};
  CachedRealSort = {};
  CachedRMSorts.fill({});
  BVSortCache.clear();
  for (auto &Cache : FPSortCaches)
    Cache.clear();
  FXPSortCache.clear();
  ArraySortCache.clear();
  SmallFunctionSortCache.clear();
  FunctionSortCache.clear();
  SmallTupleSortCache.clear();
  TupleSortCache.clear();
}

void SMTSolverImpl::noteAckBVConstBits(const SMTExprRef &Exp,
                                       const std::string &Bits) {
  // Only the Ackermann array encoding needs build-time constant values
  // (for read canonicalization); keep the default mode overhead-free.
  if (arrayMode() == ArrayEncoding::Ackermann)
    AckBVConstBits.emplace(&*Exp, Bits);
}

static std::string int64ToBits(int64_t Value, unsigned Width) {
  std::string Bits(Width, '0');
  for (unsigned I = 0; I < Width; ++I) {
    // Arithmetic shift on the signed value sign-extends, matching the
    // two's-complement semantics of mkBVFromDec for widths beyond 64.
    const int64_t Bit = I < 64 ? (Value >> I) & 1 : (Value < 0 ? 1 : 0);
    Bits[Width - 1 - I] = Bit ? '1' : '0';
  }
  return Bits;
}

void SMTSolverImpl::invalidateUnsatAssumptions() {
  LastAssumptions.clear();
  UnsatAssumptionsValid = false;
  // Fires on everything that invalidates the current model (constraint,
  // check, push, pop, reset), which is exactly the lifetime of the
  // default values handed out for unconstrained Ackermann-array queries.
  AckModelDefaults.clear();
}

void SMTSolverImpl::clearExprCaches() {
  CachedBoolExprs.fill({});
  CachedBVOne1Expr = {};
  CachedSmallBVZeroExprs.fill({});
  CachedRMBVExprs.fill({});
  for (auto &Cache : CachedSmallBVExprs)
    Cache.clear();
  SymbolExprCache.clear();
  FPSpecialExprCache.clear();
  FPConstExprCache.clear();
  LazyConstArrayRoots.clear();
  LazyConstArrayReach.clear();
  LazyArrayStores.clear();
  LazyArrayItes.clear();
  LazyTouched.clear();
  LazyConstraintLevels.assign(1, {});
  LazyRootsByIndexSort.clear();
  ObservedIndexesBySort.clear();
  ObservedIndexSeen.clear();
  ArrayEqualLinks.clear();
  ArrayEqualLinksByIndexSort.clear();
  ArrayEqualCongruenceDone.clear();
  AckArrayRoots.clear();
  AckSelectMemo.clear();
  AckBVConstBits.clear();
  IEEEBVShadow.clear();
  PendingShadowLinks.clear();
  ShadowScopeLevels.assign(1, {});
  IEEEBVFnCache.clear();
  IEEEBVAppCache.clear();
  invalidateUnsatAssumptions();
}

void SMTSolverImpl::initializeCommonSingletons() {
  CachedBoolExprs[0] = mkBool(false);
  CachedBoolExprs[1] = mkBool(true);
  CachedBVOne1Expr = mkBVFromBin("1", 1);
  CachedSmallBVZeroExprs[1] = mkBVFromBin("0", 1);
  CachedSmallBVZeroExprs[2] = mkBVFromBin("00", 2);
  CachedSmallBVZeroExprs[3] = mkBVFromBin("000", 3);
  CachedSmallBVZeroExprs[4] = mkBVFromBin("0000", 4);
  auto &CachedBVNegOneExprs = CachedSmallBVExprs[cachedSmallBVExprIndex(-1)];
  auto &CachedBVZeroExprs = CachedSmallBVExprs[cachedSmallBVExprIndex(0)];
  auto &CachedBVOneExprs = CachedSmallBVExprs[cachedSmallBVExprIndex(1)];
  CachedBVZeroExprs.resize(5);
  CachedBVZeroExprs[1] = CachedSmallBVZeroExprs[1];
  CachedBVZeroExprs[2] = CachedSmallBVZeroExprs[2];
  CachedBVZeroExprs[3] = CachedSmallBVZeroExprs[3];
  CachedBVZeroExprs[4] = CachedSmallBVZeroExprs[4];
  CachedBVOneExprs.resize(2);
  CachedBVOneExprs[1] = CachedBVOne1Expr;
  CachedBVNegOneExprs.resize(2);
  CachedBVNegOneExprs[1] = CachedBVOne1Expr;
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_EVEN)] =
      SMTSolverImpl::mkRMImpl(RM::ROUND_TO_EVEN);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_AWAY)] =
      SMTSolverImpl::mkRMImpl(RM::ROUND_TO_AWAY);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_PLUS_INF)] =
      SMTSolverImpl::mkRMImpl(RM::ROUND_TO_PLUS_INF);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_MINUS_INF)] =
      SMTSolverImpl::mkRMImpl(RM::ROUND_TO_MINUS_INF);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_ZERO)] =
      SMTSolverImpl::mkRMImpl(RM::ROUND_TO_ZERO);
}

CAMADA_DEFINE_CACHED_SORT(mkBoolSort, CachedBoolSort, isBoolSort)

CAMADA_DEFINE_CACHED_SORT(mkIntSort, CachedIntSort, isIntSort)

CAMADA_DEFINE_CACHED_SORT(mkRealSort, CachedRealSort, isRealSort)

SMTSortRef SMTSolverImpl::mkBVSort(const unsigned BitWidth) {
  fatalErrorIf(BitWidth == 0, "Bit-vector sort width must be non-zero");
  auto It = BVSortCache.find(BitWidth);
  if (It != BVSortCache.end())
    return It->second;

  SMTSortRef theSort = mkBVSortImpl(BitWidth);
  assert(theSort->isBVSort());
  assert(theSort->getWidth() == BitWidth);
  assert(theSort->getWidth() == theSort->getWidthFromSolver());
  BVSortCache.emplace(BitWidth, theSort);
  return theSort;
}

SMTSortRef SMTSolverImpl::mkRMSort(FPEncoding Encoding) {
  SMTSortRef &CachedSort = CachedRMSorts[fpEncodingIndex(Encoding)];
  if (CachedSort)
    return CachedSort;

  SMTSortRef theSort = Encoding == FPEncoding::BV
                           ? SMTSolverImpl::mkRMSortImpl()
                           : mkRMSortImpl();
  assert(theSort->isRMSort());
  CachedSort = theSort;
  return theSort;
}

SMTSortRef SMTSolverImpl::mkFPSort(const unsigned ExpWidth,
                                   const unsigned SigWidth,
                                   FPEncoding Encoding) {
  fatalErrorIf(ExpWidth == 0, "Floating-point exponent width must be non-zero");
  fatalErrorIf(SigWidth == 0,
               "Floating-point significand width must be non-zero");
  constexpr unsigned MaxWidth = std::numeric_limits<unsigned>::max();
  fatalErrorIf(SigWidth > MaxWidth - 1 || ExpWidth > MaxWidth - 1 - SigWidth,
               "Floating-point sort width overflow");
  // The BV encoding's normalization counts leading zeros of intermediates
  // up to 2*sbits + 5 bits wide (sbits = SigWidth + 1 with the hidden
  // bit; the widest is FMA's renormalize) in (ExpWidth + 2)-bit signed
  // arithmetic, so the count must fit as a positive value there. A format
  // with a wide significand and a tiny exponent would silently misround —
  // reject it at sort creation. Every IEEE format passes with orders of
  // magnitude to spare (binary32: 53 <= 511).
  fatalErrorIf(Encoding == FPEncoding::BV && ExpWidth < 31 &&
                   2 * (SigWidth + 1) + 5 > (1u << (ExpWidth + 1)) - 1,
               "Floating-point format unsupported by the BV encoding: the "
               "significand is too wide for the exponent width (requires "
               "2*(SigWidth+1) + 5 <= 2^(ExpWidth+1) - 1)");
  auto &Cache = FPSortCaches[fpEncodingIndex(Encoding)];
  FPSortCacheKey Key{ExpWidth, SigWidth};
  auto It = Cache.find(Key);
  if (It != Cache.end())
    return It->second;

  SMTSortRef theSort = Encoding == FPEncoding::BV
                           ? SMTSolverImpl::mkFPSortImpl(ExpWidth, SigWidth)
                           : mkFPSortImpl(ExpWidth, SigWidth);
  assert(theSort->isFPSort());
  assert(theSort->getWidth() == (1 + ExpWidth + SigWidth));
  assert(theSort->getWidth() == theSort->getWidthFromSolver());
  Cache.emplace(Key, theSort);
  return theSort;
}

SMTSortRef SMTSolverImpl::mkFP32Sort(FPEncoding Encoding) {
  return mkFPSort(8, 23, Encoding);
}

SMTSortRef SMTSolverImpl::mkFP64Sort(FPEncoding Encoding) {
  return mkFPSort(11, 52, Encoding);
}

SMTSortRef SMTSolverImpl::mkArraySort(const SMTSortRef &IndexSort,
                                      const SMTSortRef &ElemSort) {
  // Tuple-typed array components on backends without native datatype
  // support would route the encoded tuple's CamadaTupleSort (which has
  // no backend sort handle) through mkArraySortImpl, where the backend
  // would static_cast it as one of its own sorts. Reject up front. The
  // per-field array decomposition is tracked in issue #17.
  fatalErrorIf(sortContainsTuple(IndexSort) && !nativeTupleSupport(),
               "Arrays whose index sort involves a tuple are not supported "
               "on this backend; see issue #17");
  ArraySortCacheKey Key{IndexSort.get(), ElemSort.get()};
  auto It = ArraySortCache.find(Key);
  if (It != ArraySortCache.end())
    return It->second;

  // Element sorts involving tuples have no backend representation on
  // backends without native datatype support: the array decomposes into
  // a bundle of per-leaf-field backend arrays (see camadatuple.cpp).
  if (!nativeTupleSupport() && sortContainsTuple(ElemSort)) {
    SMTSortRef theSort = mkCamadaTupleArraySort(*this, IndexSort, ElemSort);
    assert(theSort->isArraySort());
    ArraySortCache.emplace(Key, theSort);
    return theSort;
  }

  // Ackermann mode: arrays are Camada-owned nodes with no backend sort
  // (see camadaarray.cpp). Tuple-involving element sorts were dissolved
  // above (the mode forces the Camada tuple encoding), so only scalar
  // element sorts reach this point.
  if (arrayMode() == ArrayEncoding::Ackermann) {
    SMTSortRef theSort = mkAckArraySort(IndexSort, ElemSort);
    assert(theSort->isArraySort());
    ArraySortCache.emplace(Key, theSort);
    return theSort;
  }

  SMTSortRef theSort = mkArraySortImpl(IndexSort, ElemSort);
  assert(theSort->isArraySort());
  assert(theSort->getIndexSort() == IndexSort);
  assert(theSort->getElementSort() == ElemSort);
  ArraySortCache.emplace(Key, theSort);
  return theSort;
}

SMTSortRef
SMTSolverImpl::mkFunctionSort(const std::vector<SMTSortRef> &DomainSorts,
                              const SMTSortRef &CodomainSort) {
  fatalErrorIf(DomainSorts.empty(),
               "Function sort must have at least one domain sort");
  // Tuple-typed function components on backends without native datatype
  // support would static_cast a CamadaTupleSort as a backend sort.
  // Reject up front; structural lowering is part of the issue #17 work.
  if (!nativeTupleSupport()) {
    fatalErrorIf(sortContainsTuple(CodomainSort),
                 "Functions returning tuples (or tuple-involving arrays) "
                 "are not yet supported on this backend; see issue #17");
    for (const auto &D : DomainSorts)
      fatalErrorIf(sortContainsTuple(D),
                   "Functions taking tuple (or tuple-involving array) "
                   "arguments are not yet supported on this backend; see "
                   "issue #17");
  }
  // Ackermann-mode arrays have no backend term to pass to or return from
  // an uninterpreted function.
  if (arrayMode() == ArrayEncoding::Ackermann) {
    fatalErrorIf(CodomainSort->isArraySort(),
                 "Functions returning arrays are not supported with the "
                 "Ackermann array encoding");
    for (const auto &D : DomainSorts)
      fatalErrorIf(D->isArraySort(),
                   "Functions taking array arguments are not supported "
                   "with the Ackermann array encoding");
  }
  if (DomainSorts.size() <= 4) {
    SmallFunctionSortCacheKey SmallKey{};
    SmallKey.CodomainSort = CodomainSort.get();
    SmallKey.Size = static_cast<uint8_t>(DomainSorts.size());
    for (uint8_t I = 0; I < SmallKey.Size; ++I)
      SmallKey.DomainSorts[I] = DomainSorts[I].get();

    auto It = SmallFunctionSortCache.find(SmallKey);
    if (It != SmallFunctionSortCache.end())
      return It->second;

    SMTSortRef theSort = mkFunctionSortImpl(DomainSorts, CodomainSort);
    assert(theSort->isFunctionSort());
    assert(theSort->getDomainSorts() == DomainSorts);
    assert(theSort->getCodomainSort() == CodomainSort);
    SmallFunctionSortCache.emplace(SmallKey, theSort);
    return theSort;
  }

  FunctionSortCacheKey Key{};
  Key.CodomainSort = CodomainSort.get();
  Key.DomainSorts.reserve(DomainSorts.size());
  for (const auto &Sort : DomainSorts)
    Key.DomainSorts.push_back(Sort.get());
  auto It = FunctionSortCache.find(Key);
  if (It != FunctionSortCache.end())
    return It->second;

  SMTSortRef theSort = mkFunctionSortImpl(DomainSorts, CodomainSort);
  assert(theSort->isFunctionSort());
  assert(theSort->getDomainSorts() == DomainSorts);
  assert(theSort->getCodomainSort() == CodomainSort);
  FunctionSortCache.emplace(std::move(Key), theSort);
  return theSort;
}

SMTSortRef
SMTSolverImpl::mkTupleSort(const std::vector<SMTSortRef> &ElementSorts) {
  // Route to the Camada-managed lowering for backends without native
  // datatype support; the caches still serve identity for these (the
  // CamadaTupleSort sits in the same SortArena as backend sorts).
  auto Construct = [this, &ElementSorts]() {
    return nativeTupleSupport() ? mkTupleSortImpl(ElementSorts)
                                : mkCamadaTupleSort(*this, ElementSorts);
  };

  if (ElementSorts.size() <= 4) {
    SmallTupleSortCacheKey SmallKey{};
    SmallKey.Size = static_cast<uint8_t>(ElementSorts.size());
    for (uint8_t I = 0; I < SmallKey.Size; ++I)
      SmallKey.ElementSorts[I] = ElementSorts[I].get();

    auto It = SmallTupleSortCache.find(SmallKey);
    if (It != SmallTupleSortCache.end())
      return It->second;

    SMTSortRef theSort = Construct();
    assert(theSort->isTupleSort());
    assert(theSort->getTupleElementSorts() == ElementSorts);
    SmallTupleSortCache.emplace(SmallKey, theSort);
    return theSort;
  }

  TupleSortCacheKey Key{};
  Key.ElementSorts.reserve(ElementSorts.size());
  for (const auto &Sort : ElementSorts)
    Key.ElementSorts.push_back(Sort.get());
  auto It = TupleSortCache.find(Key);
  if (It != TupleSortCache.end())
    return It->second;

  SMTSortRef theSort = Construct();
  assert(theSort->isTupleSort());
  assert(theSort->getTupleElementSorts() == ElementSorts);
  TupleSortCache.emplace(std::move(Key), theSort);
  return theSort;
}

SMTSortRef SMTSolverImpl::mkFunctionSortImpl(const std::vector<SMTSortRef> &,
                                             const SMTSortRef &) {
  unsupportedFeature("Uninterpreted functions");
}

void SMTSolverImpl::addConstraint(const SMTExprRef &Exp) {
  requireBoolSort(Exp, "Expected boolean constraint");
  invalidateUnsatAssumptions();
  commitShadowLink(Exp);
  return addConstraintImpl(Exp);
}

void SMTSolverImpl::commitShadowLink(const SMTExprRef &Constraint) {
  auto It = PendingShadowLinks.find(&*Constraint);
  if (It == PendingShadowLinks.end())
    return;
  // Keep the first (outermost) entry on collision so a pop cannot erase a
  // fact established in an outer scope; only journal what was inserted.
  if (IEEEBVShadow.emplace(It->second.Target, It->second.Bits).second)
    ShadowScopeLevels.back().push_back(It->second.Target);
}

CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVAdd,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVAddImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSub,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSubImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVMul,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVMulImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSRem,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSRemImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVURem,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVURemImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSDiv,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSDivImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUDiv,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVUDivImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVShl,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVShlImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVAshr,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVAshrImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVLshr,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVLshrImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVXor,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVXorImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVOr,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVOrImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVAnd,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVAndImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVXnor,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVXnorImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVNor,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVNorImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVNand,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVNandImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUlt,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVUltImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSlt,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSltImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUgt,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVUgtImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSgt,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSgtImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUle,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVUleImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSle,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSleImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUge,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVUgeImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSge,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSgeImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))

// The public surface follows the mkBVS*/mkBVU* naming convention of the
// other signed/unsigned BV pairs; the protected *Impl hooks keep a single
// IsSigned-parameterized entry point per operation, since every backend
// implements both signednesses in one place.
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSAddOverflow,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVAddOverflowImpl(LHS, RHS,
                                                        /*IsSigned=*/true),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUAddOverflow,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVAddOverflowImpl(LHS, RHS,
                                                        /*IsSigned=*/false),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSSubOverflow,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSubOverflowImpl(LHS, RHS,
                                                        /*IsSigned=*/true),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUSubOverflow,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSubOverflowImpl(LHS, RHS,
                                                        /*IsSigned=*/false),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSMulOverflow,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVMulOverflowImpl(LHS, RHS,
                                                        /*IsSigned=*/true),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUMulOverflow,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVMulOverflowImpl(LHS, RHS,
                                                        /*IsSigned=*/false),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSDivOverflow,
                                    requireBVSameSort(LHS, RHS),
                                    mkBVSDivOverflowImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkBVNegOverflow,
    requireBVSort(Exp, "Expected bit-vector expression"),
    mkBVNegOverflowImpl(Exp), assert(theExp->Sort->isBoolSort()))

SMTExprRef SMTSolverImpl::mkEqual(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  requireSameSort(LHS, RHS, "Expected expressions with same sort");
  // Tuple-sorted operands on backends without native datatype support
  // route through the Camada lowering, which fans out to per-field
  // equalities.
  if (LHS->Sort->isTupleSort() && !nativeTupleSupport())
    return mkCamadaTupleEqual(*this, LHS, RHS);
  if (LHS->Sort->isArraySort()) {
    // Decomposed tuple arrays compare as the conjunction of their leaf
    // equalities; each leaf re-enters this wrapper and engages the
    // normal array-equality machinery (lazy witness, STP encoding).
    if (!nativeTupleSupport() && sortContainsTuple(LHS->Sort->getElementSort()))
      return mkCamadaTupleArrayEqual(*this, LHS, RHS);
    // Ackermann-mode arrays have no backend term to hand to mkEqualImpl;
    // equality is always the witness + observed-index congruence
    // encoding, whose selects re-enter the Ackermann lowering.
    if (arrayMode() == ArrayEncoding::Ackermann)
      return mkEncodedArrayEqual(LHS, RHS);
    const bool LazyInvolved = !LazyConstArrayRoots.empty() &&
                              (reachesLazyArray(LHS) || reachesLazyArray(RHS));
    // Backends without native array extensionality (STP) cannot decide
    // array equality at all — their only array predicate is select — so
    // every array equality is lowered to the witness + observed-index
    // congruence encoding. Its witness selects also instantiate any lazy
    // defaults, so this subsumes the lazy lemma below.
    if (!nativeArrayExtensionality())
      return mkEncodedArrayEqual(LHS, RHS);
    if (LazyInvolved) {
      // Extensionality witness for lazy constant arrays. The backend
      // decides array equality natively, but a lazy root's default axiom
      // is only instantiated at observed indexes, so a model could fake a
      // difference (or agreement) at an unobserved index. The standard
      // reduction plugs this: a fresh witness index per equality, the
      // universally valid lemma
      //   LHS = RHS  \/  select(LHS, K) != select(RHS, K)
      // and default instantiation at K (done by mkArraySelect below). Any
      // model claiming LHS != RHS must now exhibit the difference at K,
      // where defaults are enforced.
      SMTExprRef Witness = mkSymbolUnchecked(
          "__CAMADA_lazyarr_ext" + std::to_string(LazyConstArrayCounter++),
          LHS->Sort->getIndexSort());
      SMTExprRef SelL = mkArraySelect(LHS, Witness);
      SMTExprRef SelR = mkArraySelect(RHS, Witness);
      SMTExprRef theEq = mkEqualImpl(LHS, RHS);
      assert(theEq->isBoolSort());
      SMTExprRef Lemma = mkOr(theEq, mkNot(mkEqual(SelL, SelR)));
      addConstraint(Lemma);
      LazyConstraintLevels.back().push_back(std::move(Lemma));
      return theEq;
    }
  }
  SMTExprRef theExp = mkEqualImpl(LHS, RHS);
  assert(theExp->isBoolSort());
  // Native-FP equality with exactly one shadowed side: if this equality
  // gets asserted top-level, the other side provably carries the same
  // bits (see IEEEBVShadow; commit happens in addConstraint).
  if (LHS->isFPSort() && !usesBVFPEncoding(LHS)) {
    auto L = IEEEBVShadow.find(&*LHS);
    auto R = IEEEBVShadow.find(&*RHS);
    const bool HasL = L != IEEEBVShadow.end();
    const bool HasR = R != IEEEBVShadow.end();
    if (HasL != HasR)
      PendingShadowLinks.emplace(
          &*theExp, PendingShadowLink{HasL ? &*RHS : &*LHS,
                                      HasL ? L->second : R->second});
  }
  return theExp;
}
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkImplies,
                                    requireBoolSameSort(LHS, RHS),
                                    mkImpliesImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkAnd,
                                    requireBoolSameSort(LHS, RHS),
                                    mkAndImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkOr,
                                    requireBoolSameSort(LHS, RHS),
                                    mkOrImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkXor,
                                    requireBoolSameSort(LHS, RHS),
                                    mkXorImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithAdd,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithAddImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithSub,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithSubImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithMul,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithMulImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithDiv,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithDivImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithMod,
                                    requireIntSameSort(LHS, RHS),
                                    mkArithModImpl(LHS, RHS),
                                    assert(theExp->isIntSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithLt,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithLtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithGt,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithGtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithLe,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithLeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithGe,
                                    requireArithSameSort(LHS, RHS),
                                    mkArithGeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkBVXnorImpl,
                                  mkBVNotImpl(mkBVXorImpl(LHS, RHS)), BVXnor)

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkBVNandImpl,
                                  mkBVNotImpl(mkBVAndImpl(LHS, RHS)), BVNand)

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkImpliesImpl, mkOrImpl(mkNotImpl(LHS), RHS),
                                  Implies)

CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPLt,
                                    requireFPSameSort(LHS, RHS),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPLtImpl(LHS, RHS)
                                        : mkFPLtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPGt,
                                    requireFPSameSort(LHS, RHS),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPGtImpl(LHS, RHS)
                                        : mkFPGtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPLe,
                                    requireFPSameSort(LHS, RHS),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPLeImpl(LHS, RHS)
                                        : mkFPLeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPGe,
                                    requireFPSameSort(LHS, RHS),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPGeImpl(LHS, RHS)
                                        : mkFPGeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPEqual,
                                    requireFPSameSort(LHS, RHS),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPEqualImpl(LHS, RHS)
                                        : mkFPEqualImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))

#undef CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkBVNeg, requireBVSort(Exp, "Expected bit-vector expression"),
    mkBVNegImpl(Exp), assert(theExp->Sort == Exp->Sort))

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkBVNot, requireBVSort(Exp, "Expected bit-vector expression"),
    mkBVNotImpl(Exp), assert(theExp->Sort == Exp->Sort))

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkNot, requireBoolSort(Exp, "Expected boolean expression"),
    mkNotImpl(Exp), assert(theExp->isBoolSort()))

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkArithNeg,
    requireArithSort(Exp, "Expected arithmetic expression"),
    mkArithNegImpl(Exp), assert(theExp->Sort == Exp->Sort))

SMTExprRef SMTSolverImpl::mkArithShl(const SMTExprRef &Exp, unsigned Amount) {
  requireIntSort(Exp, "Expected integer expression");
  SMTExprRef theExp = mkArithShlImpl(Exp, Amount);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArithShl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  requireIntSort(LHS, "Expected integer expression");
  requireIntSort(RHS, "Expected integer shift amount");
  SMTExprRef theExp = mkArithShlImpl(LHS, RHS);
  assert(theExp->isIntSort());
  return theExp;
}

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkInt2Real, requireIntSort(Exp, "Expected integer expression"),
    mkInt2RealImpl(Exp), assert(theExp->isRealSort()))

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkReal2Int,
    requireArithSort(Exp, "Expected arithmetic expression"),
    mkReal2IntImpl(Exp), assert(theExp->isIntSort()))

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkIsInt,
    requireArithSort(Exp, "Expected arithmetic expression"), mkIsIntImpl(Exp),
    assert(theExp->isBoolSort()))

SMTExprRef SMTSolverImpl::mkInt2BV(unsigned Width, const SMTExprRef &Exp) {
  fatalErrorIf(Width == 0, "Bit-vector width must be non-zero");
  requireIntSort(Exp, "Expected integer expression");
  SMTExprRef theExp = mkInt2BVImpl(Width, Exp);
  assert(theExp->isBVSort());
  assert(theExp->getWidth() == Width);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBV2Int(const SMTExprRef &Exp, bool IsSigned) {
  requireBVSort(Exp, "Expected bit-vector expression");
  SMTExprRef theExp = mkBV2IntImpl(Exp, IsSigned);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                                const SMTExprRef &F) {
  requireBoolSort(Cond, "Expected boolean condition");
  requireSameSort(T, F, "Expected ITE branches with same sort");
  // Tuple-sorted branches on backends without native datatype support
  // route through the Camada lowering, which builds an Ite-kind tuple
  // node that distributes selection over its fields lazily.
  if (T->Sort->isTupleSort() && !nativeTupleSupport())
    return mkCamadaTupleIte(*this, Cond, T, F);
  // Decomposed tuple arrays ite leaf-wise; the per-leaf ites re-enter
  // this wrapper, so the lazy-root union tracking below applies per leaf.
  if (!nativeTupleSupport() && T->Sort->isArraySort() &&
      sortContainsTuple(T->Sort->getElementSort()))
    return mkCamadaTupleArrayIte(*this, Cond, T, F);
  if (arrayMode() == ArrayEncoding::Ackermann && T->Sort->isArraySort())
    return mkAckArrayIte(Cond, T, F);
  SMTExprRef theExp = mkIteImpl(Cond, T, F);
  assert(theExp->Sort == F->Sort);
  if (!LazyConstArrayRoots.empty() && T->Sort->isArraySort()) {
    std::vector<const SMTExpr *> Roots = lazyArrayRootsOf(T);
    for (const SMTExpr *Root : lazyArrayRootsOf(F))
      if (std::find(Roots.begin(), Roots.end(), Root) == Roots.end())
        Roots.push_back(Root);
    if (!Roots.empty()) {
      LazyConstArrayReach.emplace(&*theExp, std::move(Roots));
      LazyArrayItes.emplace(&*theExp, LazyArrayIteStep{Cond, &*T, &*F});
    }
  }
  return theExp;
}

CAMADA_DEFINE_BV_EXTEND_WRAPPER(mkBVSignExt, mkBVSignExtImpl, "sign")

CAMADA_DEFINE_BV_EXTEND_WRAPPER(mkBVZeroExt, mkBVZeroExtImpl, "zero")

SMTExprRef SMTSolverImpl::mkBVExtract(unsigned High, unsigned Low,
                                      const SMTExprRef &Exp) {
  fatalErrorIf(!Exp->isBVSort() && !Exp->isFPSort(),
               "Expected bit-vector or floating-point expression");
  fatalErrorIf(High < Low, "Bit-vector extract high bit is below low bit");
  fatalErrorIf(High >= Exp->getWidth() || Low >= Exp->getWidth(),
               "Bit-vector extract range is out of bounds");
  SMTExprRef theExp = Exp->isBVSort()
                          ? mkBVExtractImpl(High, Low, Exp)
                          : mkBVExtractImpl(High, Low, mkIEEEFPToBV(Exp));
  assert(theExp->getWidth() == (High - Low + 1));
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVConcat(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  requireBVSort(LHS, "Expected bit-vector expression");
  requireBVSort(RHS, "Expected bit-vector expression");
  fatalErrorIf(LHS->getWidth() >
                   std::numeric_limits<unsigned>::max() - RHS->getWidth(),
               "Bit-vector concatenation width overflow");
  SMTExprRef theExp = mkBVConcatImpl(LHS, RHS);
  assert(theExp->getWidth() == (LHS->getWidth() + RHS->getWidth()));
  return theExp;
}

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkBVRedOr, requireBVSort(Exp, "Expected bit-vector expression"),
    mkBVRedOrImpl(Exp), assert(theExp->getWidth() == 1))

CAMADA_DEFINE_SIMPLE_UNARY_WRAPPER(
    SMTExprRef, mkBVRedAnd,
    requireBVSort(Exp, "Expected bit-vector expression"), mkBVRedAndImpl(Exp),
    assert(theExp->getWidth() == 1))

CAMADA_DEFINE_FP_UNARY_WRAPPER(
    mkFPAbs, mkFPAbsImpl,
    requireFPSort(Exp, "Expected floating-point expression"),
    assert(theExp->Sort == Exp->Sort))

SMTExprRef SMTSolverImpl::mkFPNeg(const SMTExprRef &Exp,
                                  FPNegBehavior Behavior) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPNegImpl(Exp, Behavior)
                          : mkFPNegImpl(Exp, Behavior);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

CAMADA_DEFINE_FP_UNARY_WRAPPER(
    mkFPIsInfinite, mkFPIsInfiniteImpl,
    requireFPSort(Exp, "Expected floating-point expression"),
    assert(theExp->isBoolSort()))

CAMADA_DEFINE_FP_UNARY_WRAPPER(
    mkFPIsNaN, mkFPIsNaNImpl,
    requireFPSort(Exp, "Expected floating-point expression"),
    assert(theExp->isBoolSort()))

CAMADA_DEFINE_FP_UNARY_WRAPPER(
    mkFPIsDenormal, mkFPIsDenormalImpl,
    requireFPSort(Exp, "Expected floating-point expression"),
    assert(theExp->isBoolSort()))

CAMADA_DEFINE_FP_UNARY_WRAPPER(
    mkFPIsNormal, mkFPIsNormalImpl,
    requireFPSort(Exp, "Expected floating-point expression"),
    assert(theExp->isBoolSort()))

CAMADA_DEFINE_FP_UNARY_WRAPPER(
    mkFPIsZero, mkFPIsZeroImpl,
    requireFPSort(Exp, "Expected floating-point expression"),
    assert(theExp->isBoolSort()))

CAMADA_DEFINE_FP_RM_BINARY_WRAPPER(mkFPMul, mkFPMulImpl)

CAMADA_DEFINE_FP_RM_BINARY_WRAPPER(mkFPDiv, mkFPDivImpl)

SMTExprRef SMTSolverImpl::mkFPRem(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  requireFPSameSort(LHS, RHS);
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPRemImpl(LHS, RHS)
                          : mkFPRemImpl(LHS, RHS);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

CAMADA_DEFINE_FP_RM_BINARY_WRAPPER(mkFPAdd, mkFPAddImpl)

CAMADA_DEFINE_FP_RM_BINARY_WRAPPER(mkFPSub, mkFPSubImpl)

SMTExprRef SMTSolverImpl::mkFPSqrt(const SMTExprRef &Exp, const SMTExprRef &R) {
  requireFPSort(Exp, "Expected floating-point expression");
  requireMatchingFPAndRMEncoding(Exp, R);
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPSqrtImpl(Exp, R)
                          : mkFPSqrtImpl(Exp, R);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                                  const SMTExprRef &Z, const SMTExprRef &R) {
  requireFPSameSortAndRM(X, Y, R);
  requireSameSort(Y, Z, "Expected floating-point expressions with same sort");
  SMTExprRef theExp = usesBVFPEncoding(X)
                          ? SMTSolverImpl::mkFPFMAImpl(X, Y, Z, R)
                          : mkFPFMAImpl(X, Y, Z, R);
  assert(theExp->Sort == Z->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R) {
  requireFPSort(From, "Expected floating-point expression");
  requireFPSort(To, "Expected floating-point target sort");
  requireRMSort(R, "Expected rounding-mode expression");
  fatalErrorIf(usesBVFPEncoding(From) != usesBVFPEncoding(To),
               "Floating-point source and target use different encodings");
  fatalErrorIf(
      usesBVFPEncoding(To) != usesBVRMEncoding(R),
      "Floating-point target and rounding mode use different encodings");
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkFPtoFPImpl(From, To, R)
                          : mkFPtoFPImpl(From, To, R);
  assert(theExp->Sort == To);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkSBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To, const SMTExprRef &R) {
  requireBVSort(From, "Expected bit-vector expression");
  requireFPSort(To, "Expected floating-point target sort");
  requireRMSort(R, "Expected rounding-mode expression");
  fatalErrorIf(
      usesBVFPEncoding(To) != usesBVRMEncoding(R),
      "Floating-point target and rounding mode use different encodings");
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkSBVtoFPImpl(From, To, R)
                          : mkSBVtoFPImpl(From, To, R);
  assert(theExp->Sort == To);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkUBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To, const SMTExprRef &R) {
  requireBVSort(From, "Expected bit-vector expression");
  requireFPSort(To, "Expected floating-point target sort");
  requireRMSort(R, "Expected rounding-mode expression");
  fatalErrorIf(
      usesBVFPEncoding(To) != usesBVRMEncoding(R),
      "Floating-point target and rounding mode use different encodings");
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkUBVtoFPImpl(From, To, R)
                          : mkUBVtoFPImpl(From, To, R);
  assert(theExp->Sort == To);
  return theExp;
}

CAMADA_DEFINE_FP_TO_BV_WRAPPER(mkFPtoSBV, mkFPtoSBVImpl)

CAMADA_DEFINE_FP_TO_BV_WRAPPER(mkFPtoUBV, mkFPtoUBVImpl)

SMTExprRef SMTSolverImpl::mkFPtoIntegral(const SMTExprRef &From,
                                         const SMTExprRef &R) {
  requireFPSort(From, "Expected floating-point expression");
  requireMatchingFPAndRMEncoding(From, R);
  SMTExprRef theExp = usesBVFPEncoding(From)
                          ? SMTSolverImpl::mkFPtoIntegralImpl(From, R)
                          : mkFPtoIntegralImpl(From, R);
  assert(theExp->isFPSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArraySelect(const SMTExprRef &Array,
                                        const SMTExprRef &Index) {
  fatalErrorIf(!Array->isArraySort(), "Expected array expression");
  fatalErrorIf(Array->Sort->getIndexSort() != Index->Sort,
               "Expected array index with matching sort");
  // Decomposed tuple arrays select leaf-wise; the per-leaf selects below
  // re-enter this wrapper, so observation/lazy instantiation happens per
  // leaf.
  if (!nativeTupleSupport() && sortContainsTuple(Array->Sort->getElementSort()))
    return mkCamadaTupleArraySelect(*this, Array, Index);
  if (!InLazyModelQuery)
    observeArrayIndex(Index);
  if (arrayMode() == ArrayEncoding::Ackermann) {
    // Selects built for model evaluation must not mint reads or emit
    // axioms; resolve them against the model instead.
    SMTExprRef theExp = InLazyModelQuery ? resolveAckArrayElement(Array, Index)
                                         : mkAckArraySelect(Array, Index);
    assert(theExp->Sort == Array->Sort->getElementSort());
    return theExp;
  }
  SMTExprRef theExp = mkArraySelectImpl(Array, Index);
  assert(theExp->Sort == Array->Sort->getElementSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArrayStore(const SMTExprRef &Array,
                                       const SMTExprRef &Index,
                                       const SMTExprRef &Element) {
  fatalErrorIf(!Array->isArraySort(), "Expected array expression");
  fatalErrorIf(Array->Sort->getIndexSort() != Index->Sort,
               "Expected array index with matching sort");
  fatalErrorIf(Array->Sort->getElementSort() != Element->Sort,
               "Expected array element with matching sort");
  // Decomposed tuple arrays store leaf-wise; the per-leaf stores re-enter
  // this wrapper, so the lazy guards/tracking below apply per leaf.
  if (!nativeTupleSupport() && sortContainsTuple(Array->Sort->getElementSort()))
    return mkCamadaTupleArrayStore(*this, Array, Index, Element);
  fatalErrorIf(!LazyConstArrayRoots.empty() && reachesLazyArray(Element),
               "Storing a lazily lowered constant array inside another array "
               "is not supported");
  if (arrayMode() == ArrayEncoding::Ackermann) {
    SMTExprRef theExp = mkAckArrayStore(Array, Index, Element);
    assert(theExp->Sort == Array->Sort);
    return theExp;
  }
  SMTExprRef theExp = mkArrayStoreImpl(Array, Index, Element);
  assert(theExp->Sort == Array->Sort);
  if (!LazyConstArrayRoots.empty()) {
    std::vector<const SMTExpr *> Roots = lazyArrayRootsOf(Array);
    if (!Roots.empty()) {
      LazyConstArrayReach.emplace(&*theExp, std::move(Roots));
      LazyArrayStores.emplace(&*theExp,
                              LazyArrayStoreStep{&*Array, Index, Element});
    }
  }
  return theExp;
}

std::vector<const SMTExpr *>
SMTSolverImpl::lazyArrayRootsOf(const SMTExprRef &Exp) const {
  if (LazyConstArrayRoots.count(&*Exp) != 0)
    return {&*Exp};
  auto It = LazyConstArrayReach.find(&*Exp);
  return It != LazyConstArrayReach.end() ? It->second
                                         : std::vector<const SMTExpr *>{};
}

bool SMTSolverImpl::reachesLazyArray(const SMTExprRef &Exp) const {
  return LazyConstArrayRoots.count(&*Exp) != 0 ||
         LazyConstArrayReach.count(&*Exp) != 0;
}

SMTExprRef SMTSolverImpl::mkLazyConstArray(const SMTSortRef &IndexSort,
                                           const SMTExprRef &InitValue) {
  // Nesting (array_of(array_of(v))) is supported: the outer default axiom
  // `select(Root, i) = Init` is an ASSERTED-TRUE array equality, which
  // instantiateLazyDefaultAt lowers without an extensionality witness —
  // known-true polarity has no negative direction to protect, and not
  // minting a witness per default is exactly what makes nesting terminate
  // (a witness would be observed, firing this same root's default at a
  // fresh index, forever). Reads of the nested value observe the inner
  // index, firing the inner root's default there, and the asserted
  // equality propagates it. Model extraction returns the inner lazy array
  // as the base; the consumer re-queries it via getArrayElement.
  SMTSortRef ArraySort = mkArraySort(IndexSort, InitValue->Sort);
  SMTExprRef Root = mkSymbolUnchecked(
      "__CAMADA_lazyarr" + std::to_string(LazyConstArrayCounter++), ArraySort);
  Root = rewrapExprImpl(*Root, Root->Sort, SMTExprKind::ArrayConst);
  LazyConstArrayRoots.emplace(&*Root, LazyConstArrayRoot{Root, InitValue});
  const SMTSort *IndexSortKey = &*IndexSort;
  LazyRootsByIndexSort[IndexSortKey].push_back(&*Root);
  // Replay the default axiom at every index already observed at this
  // sort: reads may reach this root through terms built before it (e.g.
  // a store over an array later equated with it).
  if (auto It = ObservedIndexesBySort.find(IndexSortKey);
      It != ObservedIndexesBySort.end()) {
    const std::vector<SMTExprRef> Observed = It->second;
    for (const SMTExprRef &Index : Observed)
      instantiateLazyDefaultAt(&*Root, Index);
  }
  return Root;
}

void SMTSolverImpl::instantiateLazyDefaultAt(const SMTExpr *RootKey,
                                             const SMTExprRef &Index) {
  // Memo-first: the select built below re-enters mkArraySelect (and
  // observeArrayIndex) and must find the pair already recorded.
  if (!LazyTouched.insert({RootKey, &*Index}).second)
    return;
  // Copy: the maps may rehash while the constraint is built.
  const LazyConstArrayRoot Root = LazyConstArrayRoots.at(RootKey);
  SMTExprRef Sel = mkArraySelect(Root.Root, Index);
  SMTExprRef Constraint;
  if (Root.Init->isArraySort()) {
    // Nested lazy const array: the default is an ASSERTED-TRUE array
    // equality, so it needs no extensionality witness — there is no
    // negative direction a model could fake. Going through the public
    // mkEqual would mint one, whose observation re-fires this same
    // root's default at the fresh witness, unboundedly; the direct
    // native equality is both sound (the backend enforces it
    // extensionally, and Init's own defaults fire at every observed
    // inner index) and what makes nesting terminate. STP cannot build
    // nested array sorts at all, so the non-extensional case is
    // unreachable here.
    fatalErrorIf(!nativeArrayExtensionality(),
                 "Nested lazy constant arrays require native array "
                 "extensionality");
    Constraint = mkEqualImpl(Sel, Root.Init);
  } else {
    Constraint = mkEqual(Sel, Root.Init);
  }
  addConstraint(Constraint);
  LazyConstraintLevels.back().push_back(std::move(Constraint));
}

std::string SMTSolverImpl::lazyIndexModelBits(const SMTExprRef &Exp) {
  if (Exp->isBoolSort()) {
    SMTResult<bool> Value = getBool(Exp);
    return Value ? std::string(Value.value() ? "1" : "0") : std::string();
  }
  if (!Exp->isBVSort())
    return std::string(); // unsupported index sort: backend fallback
  SMTResult<std::string> Value = getBVInBin(Exp);
  return Value ? Value.value() : std::string();
}

void SMTSolverImpl::observeArrayIndex(const SMTExprRef &Index) {
  const SMTSort *SortKey = &*Index->Sort;
  if (!ObservedIndexSeen.insert({SortKey, &*Index}).second)
    return;
  ObservedIndexesBySort[SortKey].push_back(Index);
  // Copies throughout: instantiation builds selects that re-enter this
  // function and may register new roots/links/indexes.
  if (auto It = LazyRootsByIndexSort.find(SortKey);
      It != LazyRootsByIndexSort.end()) {
    const std::vector<const SMTExpr *> Roots = It->second;
    for (const SMTExpr *RootKey : Roots)
      instantiateLazyDefaultAt(RootKey, Index);
  }
  if (auto It = ArrayEqualLinksByIndexSort.find(SortKey);
      It != ArrayEqualLinksByIndexSort.end()) {
    const std::vector<std::size_t> Links = It->second;
    for (std::size_t LinkId : Links)
      assertArrayEqualCongruence(LinkId, Index);
  }
}

SMTExprRef SMTSolverImpl::mkEncodedArrayEqual(const SMTExprRef &LHS,
                                              const SMTExprRef &RHS) {
  const std::size_t LinkId = ArrayEqualLinks.size();
  SMTExprRef EqVar = mkSymbolUnchecked(
      "__CAMADA_arreq" + std::to_string(ArrayEqualCounter++), mkBoolSort());
  // Present the lowering as an Equal node, like the other common-layer
  // lowerings do.
  EqVar = rewrapExprImpl(*EqVar, EqVar->Sort, SMTExprKind::Equal);
  ArrayEqualLinks.push_back(ArrayEqualLink{EqVar, LHS, RHS});
  const SMTSort *IndexSortKey = &*LHS->Sort->getIndexSort();
  ArrayEqualLinksByIndexSort[IndexSortKey].push_back(LinkId);

  // Positive direction at every index already observed at this sort —
  // reads may reach these arrays through derived terms or terms built
  // before this equality. (Future indexes fire through observeArrayIndex.)
  if (auto It = ObservedIndexesBySort.find(IndexSortKey);
      It != ObservedIndexesBySort.end()) {
    const std::vector<SMTExprRef> Observed = It->second;
    for (const SMTExprRef &Index : Observed)
      assertArrayEqualCongruence(LinkId, Index);
  }

  // Negative direction: a claimed difference must be exhibitable at the
  // witness. The selects below also flow through mkArraySelect, which
  // asserts this link's congruence at W and instantiates lazy defaults,
  // so EqVar is fully tied to the arrays' contents at W.
  SMTExprRef Witness = mkSymbolUnchecked(
      "__CAMADA_arreq_wit" + std::to_string(ArrayEqualCounter++),
      LHS->Sort->getIndexSort());
  SMTExprRef Lemma = mkOr(EqVar, mkNot(mkEqual(mkArraySelect(LHS, Witness),
                                               mkArraySelect(RHS, Witness))));
  addConstraint(Lemma);
  LazyConstraintLevels.back().push_back(std::move(Lemma));
  return EqVar;
}

void SMTSolverImpl::assertArrayEqualCongruence(std::size_t LinkId,
                                               const SMTExprRef &Index) {
  if (!ArrayEqualCongruenceDone.insert({LinkId, &*Index}).second)
    return;
  const ArrayEqualLink Link = ArrayEqualLinks[LinkId];
  SMTExprRef Constraint =
      mkImplies(Link.EqVar, mkEqual(mkArraySelect(Link.LHS, Index),
                                    mkArraySelect(Link.RHS, Index)));
  addConstraint(Constraint);
  LazyConstraintLevels.back().push_back(std::move(Constraint));
}

SMTExprRef SMTSolverImpl::resolveLazyArrayElement(const SMTExprRef &Array,
                                                  const SMTExprRef &Index) {
  // Post-check model query: the solver's model is unconstrained at indexes
  // whose defaults were never instantiated, so answer from the tracked
  // derivation chain instead. Returns a null ref when the chain cannot be
  // resolved, in which case the caller falls back to the backend.
  const auto modelBits = [this](const SMTExprRef &E) {
    return lazyIndexModelBits(E);
  };

  const std::string QueryBits = modelBits(Index);
  if (QueryBits.empty())
    return {};

  const SMTExpr *Cur = &*Array;
  while (true) {
    if (auto It = LazyArrayStores.find(Cur); It != LazyArrayStores.end()) {
      const std::string StepBits = modelBits(It->second.Index);
      if (StepBits.empty())
        return {};
      if (StepBits == QueryBits)
        return It->second.Value;
      Cur = It->second.Parent;
      continue;
    }
    if (auto It = LazyArrayItes.find(Cur); It != LazyArrayItes.end()) {
      SMTResult<bool> Cond = getBool(It->second.Cond);
      if (!Cond)
        return {};
      Cur = Cond.value() ? It->second.TrueArr : It->second.FalseArr;
      continue;
    }
    if (auto It = LazyConstArrayRoots.find(Cur);
        It != LazyConstArrayRoots.end())
      return It->second.Init;
    return {};
  }
}

SMTExprRef SMTSolverImpl::mkTuple(const std::vector<SMTExprRef> &Elements) {
  if (!nativeTupleSupport())
    return mkCamadaTuple(*this, Elements);

  // A lazy array inside a native tuple would escape the lazy tracking:
  // tuple equality and tuple selects would bypass the default-axiom
  // instantiation. The Camada tuple lowering above composes fine.
  if (!LazyConstArrayRoots.empty())
    for (const auto &Element : Elements)
      fatalErrorIf(Element->isArraySort() && reachesLazyArray(Element),
                   "Lazily lowered constant arrays inside native tuples are "
                   "not supported");

  std::vector<SMTSortRef> ElementSorts;
  ElementSorts.reserve(Elements.size());
  for (const auto &Element : Elements)
    ElementSorts.push_back(Element->Sort);
  [[maybe_unused]] SMTSortRef TupleSort = mkTupleSort(ElementSorts);
  SMTExprRef theExp = mkTupleImpl(Elements);
  assert(theExp->Sort == TupleSort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkTupleSelect(const SMTExprRef &Tuple,
                                        unsigned Index) {
  fatalErrorIf(!Tuple->Sort->isTupleSort(), "Expected tuple expression");
  fatalErrorIf(Index >= Tuple->Sort->getTupleElementSorts().size(),
               "Tuple element index is out of bounds");
  if (!nativeTupleSupport())
    return mkCamadaTupleSelect(*this, Tuple, Index);
  SMTExprRef theExp = mkTupleSelectImpl(Tuple, Index);
  assert(theExp->Sort == Tuple->Sort->getTupleElementSorts()[Index]);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkTupleUpdate(const SMTExprRef &Tuple, unsigned Index,
                                        const SMTExprRef &Value) {
  fatalErrorIf(!Tuple->Sort->isTupleSort(), "Expected tuple expression");
  fatalErrorIf(Index >= Tuple->Sort->getTupleElementSorts().size(),
               "Tuple element index is out of bounds");
  fatalErrorIf(Tuple->Sort->getTupleElementSorts()[Index] != Value->Sort,
               "Expected tuple update value with the element's sort");
  SMTExprRef theExp = mkTupleUpdateImpl(Tuple, Index, Value);
  assert(theExp->Sort == Tuple->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkTupleUpdateImpl(const SMTExprRef &Tuple,
                                            unsigned Index,
                                            const SMTExprRef &Value) {
  const std::size_t ElementCount = Tuple->Sort->getTupleElementSorts().size();
  std::vector<SMTExprRef> Elements;
  Elements.reserve(ElementCount);
  for (unsigned I = 0; I < ElementCount; ++I)
    Elements.push_back(I == Index ? Value : mkTupleSelect(Tuple, I));
  return mkTuple(Elements);
}

SMTExprRef SMTSolverImpl::mkApply(const SMTExprRef &Function,
                                  const std::vector<SMTExprRef> &Args) {
  fatalErrorIf(!Function->isFunctionSort(), "Expected function expression");
  fatalErrorIf(Function->Sort->getDomainSorts().size() != Args.size(),
               "Function application argument count mismatch");
  for (std::size_t i = 0; i < Args.size(); ++i)
    fatalErrorIf(Function->Sort->getDomainSorts()[i] != Args[i]->Sort,
                 "Function application argument sort mismatch");
  // Uninterpreted functions observe whole arrays, not selected indexes, so
  // a lazy array argument would escape the default-axiom instantiation.
  if (!LazyConstArrayRoots.empty())
    for (const auto &Arg : Args)
      fatalErrorIf(Arg->isArraySort() && reachesLazyArray(Arg),
                   "Lazily lowered constant arrays as uninterpreted-function "
                   "arguments are not supported");
  SMTExprRef theExp = mkApplyImpl(Function, Args);
  assert(theExp->Sort == Function->Sort->getCodomainSort());
  return theExp;
}

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkApplyImpl,
                               "Uninterpreted functions", const SMTExprRef &,
                               const std::vector<SMTExprRef> &)

SMTExprRef SMTSolverImpl::mkForall(const std::vector<SMTExprRef> &Vars,
                                   const SMTExprRef &Body) {
  requireBoolSort(Body, "Expected boolean quantifier body");
  // Every quantifier is rejected in Ackermann mode, not just those over
  // array terms: a select at a bound index lowers to a nullary read
  // variable, silently losing the dependence on the bound variable, and
  // the body's provenance cannot be inspected here.
  fatalErrorIf(arrayMode() == ArrayEncoding::Ackermann,
               "Quantifiers are not supported with the Ackermann array "
               "encoding (quantifier-free formulas only)");
  // Encoded tuple variables would reach the backend's mkForallImpl as a
  // CamadaTupleExpr without a backend term, which the backend would
  // then static_cast as one of its own expressions. Reject up front.
  if (!nativeTupleSupport())
    for (const auto &V : Vars)
      fatalErrorIf(sortContainsTuple(V->Sort),
                   "Quantifiers over tuple-typed (or tuple-involving-array) "
                   "variables are not yet supported on this backend; see "
                   "issue #17");
  SMTExprRef theExp = mkForallImpl(Vars, Body);
  assert(theExp->isBoolSort());
  return theExp;
}

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkForallImpl, "Quantifiers",
                               const std::vector<SMTExprRef> &,
                               const SMTExprRef &)

SMTExprRef SMTSolverImpl::mkExists(const std::vector<SMTExprRef> &Vars,
                                   const SMTExprRef &Body) {
  requireBoolSort(Body, "Expected boolean quantifier body");
  fatalErrorIf(arrayMode() == ArrayEncoding::Ackermann,
               "Quantifiers are not supported with the Ackermann array "
               "encoding (quantifier-free formulas only)");
  if (!nativeTupleSupport())
    for (const auto &V : Vars)
      fatalErrorIf(sortContainsTuple(V->Sort),
                   "Quantifiers over tuple-typed (or tuple-involving-array) "
                   "variables are not yet supported on this backend; see "
                   "issue #17");
  SMTExprRef theExp = mkExistsImpl(Vars, Body);
  assert(theExp->isBoolSort());
  return theExp;
}

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkExistsImpl, "Quantifiers",
                               const std::vector<SMTExprRef> &,
                               const SMTExprRef &)

CAMADA_DEFINE_MODEL_GETTER(bool, getBool,
                           requireBoolSort(Exp, "Expected boolean expression"),
                           getBoolImpl)

CAMADA_DEFINE_MODEL_GETTER(int64_t, getBV,
                           requireBVSort(Exp, "Expected bit-vector expression"),
                           getBVImpl)

SMTResult<std::string> SMTSolverImpl::getBVInBin(const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  SMTResult<std::string> result = getBVInBinImpl(Exp);
  if (!result)
    return result.error();
  return addLeadingZeroes(result.value(), Exp->getWidth());
}

SMTResult<std::string> SMTSolverImpl::getInt(const SMTExprRef &Exp) {
  fatalErrorIf(!Exp->isIntSort() && !Exp->isRealSort(),
               "Expected integer or real expression");
  return getIntImpl(Exp);
}

SMTResult<std::pair<std::string, std::string>>
SMTSolverImpl::getRational(const SMTExprRef &Exp) {
  fatalErrorIf(!Exp->isRealSort(), "Expected real expression");
  return getRationalImpl(Exp);
}

SMTResult<std::pair<std::string, std::string>>
SMTSolverImpl::getRationalImpl(const SMTExprRef &Exp) {
  return SMTError{SMTErrorCode::UnsupportedOperation, Exp->getBackendKind(),
                  "Real arithmetic is not supported by this backend"};
}

SMTResult<std::string> SMTSolverImpl::getRealNumerator(const SMTExprRef &Exp) {
  fatalErrorIf(!Exp->isRealSort(), "Expected real expression");
  SMTResult<std::pair<std::string, std::string>> result = getRationalImpl(Exp);
  if (!result)
    return result.error();
  return result.value().first;
}

SMTResult<std::string>
SMTSolverImpl::getRealDenominator(const SMTExprRef &Exp) {
  fatalErrorIf(!Exp->isRealSort(), "Expected real expression");
  SMTResult<std::pair<std::string, std::string>> result = getRationalImpl(Exp);
  if (!result)
    return result.error();
  return result.value().second;
}

SMTResult<std::string> SMTSolverImpl::getFPInBin(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTResult<std::string> result = usesBVFPEncoding(Exp)
                                      ? SMTSolverImpl::getFPInBinImpl(Exp)
                                      : getFPInBinImpl(Exp);
  if (!result)
    return result.error();
  return addLeadingZeroes(result.value(), Exp->getWidth());
}

CAMADA_DEFINE_MODEL_GETTER(float, getFP32,
                           requireFPSort(Exp,
                                         "Expected floating-point expression"),
                           getFP32Impl)

CAMADA_DEFINE_MODEL_GETTER(double, getFP64,
                           requireFPSort(Exp,
                                         "Expected floating-point expression"),
                           getFP64Impl)

SMTExprRef SMTSolverImpl::getArrayElement(const SMTExprRef &Array,
                                          const SMTExprRef &Index) {
  fatalErrorIf(!Array->isArraySort(), "Expected array expression");
  fatalErrorIf(Array->Sort->getIndexSort() != Index->Sort,
               "Expected array index with matching sort");
  // Decomposed tuple arrays read each leaf at Index and reassemble the
  // per-leaf values into a tuple; the per-leaf reads re-enter this wrapper.
  if (!nativeTupleSupport() && sortContainsTuple(Array->Sort->getElementSort()))
    return getCamadaTupleArrayElement(*this, Array, Index);
  // Ackermann-mode arrays have no backend term to evaluate; resolve from
  // the tracked derivation chain and the reads of the equality class.
  if (arrayMode() == ArrayEncoding::Ackermann)
    return resolveAckArrayElement(Array, Index);
  if (!LazyConstArrayRoots.empty() && reachesLazyArray(Array))
    if (SMTExprRef Resolved = resolveLazyArrayElement(Array, Index))
      return Resolved;
  // RAII: backend model queries can throw (z3::exception,
  // CVC5ApiException); the flag must not stay latched or every later
  // select would silently skip instantiation.
  struct ModelQueryGuard {
    bool &Flag;
    bool Saved;
    explicit ModelQueryGuard(bool &F) : Flag(F), Saved(F) { F = true; }
    ~ModelQueryGuard() { Flag = Saved; }
  } Guard(InLazyModelQuery);
  SMTExprRef theExp = getArrayElementImpl(Array, Index);
  assert(theExp->Sort == Array->Sort->getElementSort());
  return theExp;
}

SMTResult<ArrayModel> SMTSolverImpl::getArrayValues(const SMTExprRef &Array) {
  fatalErrorIf(!Array->isArraySort(), "Expected array expression");
  // Decomposed tuple arrays zip the per-leaf sparse models into one
  // tuple-valued model; the per-leaf queries re-enter this wrapper.
  if (!nativeTupleSupport() && sortContainsTuple(Array->Sort->getElementSort()))
    return getCamadaTupleArrayValues(*this, Array);
  if (arrayMode() == ArrayEncoding::Ackermann)
    return ackArrayModel(Array);
  if (!LazyConstArrayRoots.empty() && reachesLazyArray(Array))
    return lazyArrayModel(Array);
  return getArrayValuesImpl(Array);
}

SMTResult<ArrayModel> SMTSolverImpl::lazyArrayModel(const SMTExprRef &Array) {
  // The backend's model is unconstrained at indexes whose lazy defaults
  // were never instantiated, so walk the tracked derivation chain instead:
  // stores become entries (outermost first, so shadowed stores at the same
  // model index are skipped), ites follow the model's branch, and the
  // reached root's initializer becomes the default.
  ArrayModel Model;
  std::set<std::string> SeenIndexBits;
  const SMTExpr *Cur = &*Array;
  while (true) {
    if (auto It = LazyArrayStores.find(Cur); It != LazyArrayStores.end()) {
      const std::string StepBits = lazyIndexModelBits(It->second.Index);
      if (StepBits.empty())
        return SMTError{SMTErrorCode::BackendError,
                        CachedBoolExprs[0]->getBackendKind(),
                        "Could not evaluate a store index while walking a "
                        "lazily lowered array model"};
      if (SeenIndexBits.insert(StepBits).second)
        Model.Entries.emplace_back(It->second.Index, It->second.Value);
      Cur = It->second.Parent;
      continue;
    }
    if (auto It = LazyArrayItes.find(Cur); It != LazyArrayItes.end()) {
      SMTResult<bool> Cond = getBool(It->second.Cond);
      if (!Cond)
        return Cond.error();
      Cur = Cond.value() ? It->second.TrueArr : It->second.FalseArr;
      continue;
    }
    if (auto It = LazyConstArrayRoots.find(Cur);
        It != LazyConstArrayRoots.end()) {
      Model.Base = It->second.Init;
      return Model;
    }
    return SMTError{SMTErrorCode::BackendError,
                    CachedBoolExprs[0]->getBackendKind(),
                    "Untracked derivation while walking a lazily lowered "
                    "array model"};
  }
}

SMTResult<ArrayModel> SMTSolverImpl::getArrayValuesImpl(const SMTExprRef &) {
  return SMTError{SMTErrorCode::UnsupportedOperation,
                  CachedBoolExprs[0]->getBackendKind(),
                  "Array model extraction is not supported by this backend"};
}

SMTExprKind SMTSolverImpl::valueKindForSort(const SMTSortRef &Sort) {
  if (Sort->isBoolSort())
    return SMTExprKind::BoolConst;
  if (Sort->isBVSort())
    return SMTExprKind::BVConst;
  if (Sort->isFPSort())
    return SMTExprKind::FPConst;
  if (Sort->isRMSort())
    return SMTExprKind::RMConst;
  if (Sort->isArraySort())
    return SMTExprKind::ArrayConst;
  if (Sort->isIntSort())
    return SMTExprKind::IntConst;
  if (Sort->isRealSort())
    return SMTExprKind::RealConst;
  return SMTExprKind::Unknown;
}

SMTExprRef SMTSolverImpl::mkBool(const bool b) {
  SMTExprRef &CachedExpr = CachedBoolExprs[b];
  if (CachedExpr)
    return CachedExpr;

  SMTExprRef theExp = mkBoolImpl(b);
  assert(theExp->isBoolSort());
  CachedExpr = theExp;
  return CachedExpr;
}

CAMADA_DEFINE_CONST_CTOR(mkInt, (int64_t v), (v), assert(theExp->isIntSort()))

CAMADA_DEFINE_CONST_CTOR(mkInt, (const std::string &v), (v),
                         assert(theExp->isIntSort()))

CAMADA_DEFINE_CONST_CTOR(mkReal, (const std::string &v), (v),
                         assert(theExp->isRealSort()))

CAMADA_DEFINE_CONST_CTOR(mkReal, (int64_t v), (v), assert(theExp->isRealSort()))

CAMADA_DEFINE_CONST_CTOR(mkReal, (int64_t num, int64_t den), (num, den),
                         assert(theExp->isRealSort()))

SMTExprRef SMTSolverImpl::mkBVFromDec(const int64_t Int,
                                      const SMTSortRef &Sort) {
  fatalErrorIf(!Sort->isBVSort(),
               "Bit-vector decimal literal sort must be bit-vector");
  const bool IsBV = Sort->getSortKind() == SMTSortKind::BV;
  if (IsBV) {
    const unsigned Width = Sort->getWidth();
    if (Int == 0 && Width < CachedSmallBVZeroExprs.size())
      return CachedSmallBVZeroExprs[Width];
    if (Int == 1 && Width == 1)
      return CachedBVOne1Expr;

    if (Int >= -1 && Int <= 1) {
      auto &Cache = CachedSmallBVExprs[cachedSmallBVExprIndex(Int)];
      if (Cache.size() <= Width)
        Cache.resize(Width + 1);

      SMTExprRef &CachedExpr = Cache[Width];
      if (CachedExpr)
        return CachedExpr;

      SMTExprRef theExp = mkBVFromDecImpl(Int, Sort);
      assert(theExp->isBVSort());
      assert(theExp->getWidth() == Width);
      noteAckBVConstBits(theExp, int64ToBits(Int, Width));
      CachedExpr = theExp;
      return CachedExpr;
    }
  }

  SMTExprRef theExp = mkBVFromDecImpl(Int, Sort);
  assert(theExp->isBVSort());
  assert(theExp->getWidth() == Sort->getWidth());
  noteAckBVConstBits(theExp, int64ToBits(Int, Sort->getWidth()));
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVFromDec(const int64_t Int, unsigned BitWidth) {
  return mkBVFromDec(Int, mkBVSort(BitWidth));
}

SMTExprRef SMTSolverImpl::mkBVFromBin(const std::string &Int,
                                      const SMTSortRef &Sort) {
  fatalErrorIf(!Sort->isBVSort(),
               "Bit-vector binary literal sort must be bit-vector");
  fatalErrorIf(Int.empty(), "Bit-vector binary literal must be non-empty");
  fatalErrorIf(!isBinaryLiteral(Int),
               "Bit-vector binary literal must contain only 0 or 1");
  fatalErrorIf(Int.length() != Sort->getWidth(),
               "Bit-vector binary literal width must match sort width");
  SMTExprRef theExp = mkBVFromBinImpl(Int, Sort);
  assert(theExp->isBVSort());
  assert(theExp->getWidth() == Sort->getWidth());
  noteAckBVConstBits(theExp, Int);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVFromBin(const std::string &Int,
                                      unsigned BitWidth) {
  return mkBVFromBin(Int, mkBVSort(BitWidth));
}

SMTExprRef SMTSolverImpl::mkBVFromBin(const std::string &Int) {
  fatalErrorIf(Int.length() > static_cast<std::size_t>(
                                  std::numeric_limits<unsigned>::max()),
               "Bit-vector binary literal width is too large");
  return mkBVFromBin(Int, Int.length());
}

SMTExprRef SMTSolverImpl::mkSymbol(const std::string &Name,
                                   const SMTSortRef &Sort) {
  // The `__CAMADA_` prefix is reserved for the symbols Camada's own
  // encodings introduce — tuple fields, lazy and Ackermann arrays, array
  // equality witnesses, FP-to-BV shadowing, int-to-BV, assumption
  // literals and quantifier variables. A user name with that prefix
  // would alias one of them and silently corrupt whichever encoding it
  // collided with; reject up front.
  fatalErrorIf(Name.compare(0, 9, "__CAMADA_") == 0,
               "Symbol names with the reserved __CAMADA_ prefix are not "
               "permitted; rename the symbol");
  return mkSymbolUnchecked(Name, Sort);
}

SMTExprRef SMTSolverImpl::mkSymbolUnchecked(const std::string &Name,
                                            const SMTSortRef &Sort) {
  SymbolExprCacheKey Key{Sort.get(), Name};
  auto Cached = SymbolExprCache.find(Key);
  if (Cached != SymbolExprCache.end())
    return Cached->second;

  // Route tuple-typed symbols to the Camada-managed lowering on backends
  // without native datatype support.
  if (Sort->isTupleSort() && !nativeTupleSupport()) {
    SMTExprRef theExp = mkCamadaTupleSymbol(*this, Name, Sort);
    SymbolExprCache.emplace(Key, theExp);
    return theExp;
  }
  if (!nativeTupleSupport() && Sort->isArraySort() &&
      sortContainsTuple(Sort->getElementSort())) {
    SMTExprRef theExp = mkCamadaTupleArraySymbol(*this, Name, Sort);
    SymbolExprCache.emplace(Key, theExp);
    return theExp;
  }
  // Ackermann mode: array symbols are roots of the read/congruence
  // encoding, never backend terms.
  if (arrayMode() == ArrayEncoding::Ackermann && Sort->isArraySort()) {
    SMTExprRef theExp = mkAckArraySymbol(Name, Sort);
    SymbolExprCache.emplace(Key, theExp);
    return theExp;
  }

  SMTExprRef theExp = mkSymbolImpl(Name, Sort);
  assert(theExp->Sort == Sort);
  SymbolExprCache.emplace(Key, theExp);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPFromBin(const std::string &FP, unsigned EWidth,
                                      FPEncoding Encoding) {
  fatalErrorIf(EWidth == 0, "Floating-point exponent width must be non-zero");
  fatalErrorIf(FP.length() <= static_cast<std::size_t>(EWidth) + 1,
               "Floating-point binary literal must include sign, exponent, and "
               "significand bits");
  fatalErrorIf(!isBinaryLiteral(FP),
               "Floating-point binary literal must contain only 0 or 1");
  const std::size_t SigWidth = FP.length() - EWidth - 1;
  fatalErrorIf(
      SigWidth > static_cast<std::size_t>(std::numeric_limits<unsigned>::max()),
      "Floating-point significand width is too large");
  SMTSortRef Sort = mkFPSort(EWidth, static_cast<unsigned>(SigWidth), Encoding);
  FPConstExprCacheKey Key{Sort.get(), FP};
  auto Cached = FPConstExprCache.find(Key);
  if (Cached != FPConstExprCache.end())
    return Cached->second;

  SMTExprRef theExp = usesBVFPEncoding(Sort)
                          ? SMTSolverImpl::mkFPFromBinImpl(FP, EWidth)
                          : mkFPFromBinImpl(FP, EWidth);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == FP.length());
  // The bits of a native-FP constant are known here and nowhere else;
  // remember them so mkIEEEFPToBV round-trips exactly, NaN payloads
  // included (see IEEEBVShadow).
  if (!usesBVFPEncoding(Sort))
    IEEEBVShadow.emplace(&*theExp,
                         mkBVFromBin(FP, static_cast<unsigned>(FP.length())));
  FPConstExprCache.emplace(std::move(Key), theExp);
  return theExp;
}

CAMADA_DEFINE_CONST_CTOR(mkFP32, (const float Float, FPEncoding Encoding),
                         (Float, Encoding), assert(theExp->isFPSort());
                         assert(theExp->getWidth() == 32))

CAMADA_DEFINE_CONST_CTOR(mkFP64, (const double Double, FPEncoding Encoding),
                         (Double, Encoding), assert(theExp->isFPSort());
                         assert(theExp->getWidth() == 64))

SMTExprRef SMTSolverImpl::mkRM(const RM &R, FPEncoding Encoding) {
  SMTExprRef theExp =
      Encoding == FPEncoding::BV ? SMTSolverImpl::mkRMImpl(R) : mkRMImpl(R);
  assert(theExp->isRMSort());
  return theExp;
}

CAMADA_DEFINE_FP_SPECIAL_VALUE(mkNaN, mkNaNImpl)

SMTExprRef SMTSolverImpl::mkNaN32(const bool Sgn, FPEncoding Encoding) {
  return mkNaN(Sgn, 8, 24, Encoding);
}

SMTExprRef SMTSolverImpl::mkNaN64(const bool Sgn, FPEncoding Encoding) {
  return mkNaN(Sgn, 11, 53, Encoding);
}

CAMADA_DEFINE_FP_SPECIAL_VALUE(mkInf, mkInfImpl)

SMTExprRef SMTSolverImpl::mkInf32(const bool Sgn, FPEncoding Encoding) {
  return mkInf(Sgn, 8, 24, Encoding);
}

SMTExprRef SMTSolverImpl::mkInf64(const bool Sgn, FPEncoding Encoding) {
  return mkInf(Sgn, 11, 53, Encoding);
}

SMTExprRef SMTSolverImpl::mkArrayConst(const SMTSortRef &IndexSort,
                                       const SMTExprRef &InitValue) {
  return mkArrayConst(IndexSort, InitValue, ConstArrayLowering::Auto);
}

SMTExprRef SMTSolverImpl::mkArrayConst(const SMTSortRef &IndexSort,
                                       const SMTExprRef &InitValue,
                                       ConstArrayLowering Lowering) {
  fatalErrorIf(!nativeTupleSupport() && sortContainsTuple(IndexSort),
               "Arrays whose index sort involves a tuple are not supported "
               "on this backend; see issue #17");
  if (Lowering == ConstArrayLowering::Auto)
    Lowering = nativeConstArraySupport() ? ConstArrayLowering::Native
                                         : ConstArrayLowering::Lazy;
  // In Ackermann mode the lowering choice is moot (see below), so an
  // explicit Native request is not an error on backends without native
  // constant arrays.
  fatalErrorIf(Lowering == ConstArrayLowering::Native &&
                   !nativeConstArraySupport() &&
                   arrayMode() != ArrayEncoding::Ackermann,
               "Native constant arrays are not supported by this backend");
  // Tuple-involving initializers decompose into one constant array per
  // scalar leaf; the per-leaf calls re-enter this wrapper, so the resolved
  // lowering (and its lazy machinery) applies per leaf.
  if (!nativeTupleSupport() && sortContainsTuple(InitValue->Sort))
    return mkCamadaTupleArrayConst(*this, IndexSort, InitValue, Lowering);
  // Ackermann mode: the lowering choice is moot — a Const node's selects
  // return the initializer directly, which is exactly what both Native
  // and Lazy promise.
  if (arrayMode() == ArrayEncoding::Ackermann) {
    SMTExprRef theExp = mkAckArrayConst(IndexSort, InitValue);
    assert(theExp->isArraySort());
    assert(theExp->Sort->getIndexSort() == IndexSort);
    assert(theExp->Sort->getElementSort() == InitValue->Sort);
    return theExp;
  }
  SMTExprRef theExp = Lowering == ConstArrayLowering::Native
                          ? mkArrayConstImpl(IndexSort, InitValue)
                          : mkLazyConstArray(IndexSort, InitValue);
  assert(theExp->isArraySort());
  assert(theExp->Sort->getIndexSort() == IndexSort);
  assert(theExp->Sort->getElementSort() == InitValue->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVToIEEEFP(const SMTExprRef &Exp,
                                       const SMTSortRef &To) {
  requireBVSort(Exp, "Expected bit-vector expression");
  requireFPSort(To, "Expected floating-point target sort");
  fatalErrorIf(Exp->getWidth() != To->getWidth(),
               "Bit-vector and floating-point target widths must match");
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkBVToIEEEFPImpl(Exp, To)
                          : mkBVToIEEEFPImpl(Exp, To);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == Exp->getWidth());
  // Remember the bits this native-FP term was built from, so a later
  // mkIEEEFPToBV round-trips exactly (see IEEEBVShadow). BV-encoded FP is
  // already exact (the base mkIEEEFPToBVImpl retags the same term), and
  // only a plain-BV source can be handed back by mkIEEEFPToBV.
  if (!usesBVFPEncoding(To) && Exp->Sort->getSortKind() == SMTSortKind::BV)
    IEEEBVShadow.emplace(&*theExp, Exp);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIEEEFPToBVViaUF(const SMTExprRef &Exp) {
  // Emulate the fp->bv primitive as a per-sort uninterpreted FUNCTION,
  // not a per-call constant: functional congruence then forces
  // value-equal terms to report equal bits, the same guarantee z3's
  // native fp.to_ieee_bv provides. The per-term tie `to_fp(fn(x)) == x`
  // pins the exact bits wherever the encoding is injective (everything
  // but NaN); at NaN the payload is unspecified but consistent. The tie
  // is a definitional, scope-independent fact — journal it so pop()
  // re-asserts it, keeping the application memo valid across scopes.
  if (auto It = IEEEBVAppCache.find(&*Exp); It != IEEEBVAppCache.end())
    return It->second;
  auto [FnIt, Inserted] = IEEEBVFnCache.try_emplace(&*Exp->Sort);
  if (Inserted)
    FnIt->second = mkSymbolUnchecked(
        "__CAMADA_ieeebv_fn" + std::to_string(IEEEBVFnCache.size() - 1),
        mkFunctionSort({Exp->Sort}, mkBVSort(Exp->getWidth())));
  SMTExprRef Bits = mkApply(FnIt->second, {Exp});
  IEEEBVAppCache.emplace(&*Exp, Bits);
  SMTExprRef Tie = mkEqual(mkBVToIEEEFP(Bits, Exp->Sort), Exp);
  addConstraint(Tie);
  LazyConstraintLevels.back().push_back(std::move(Tie));
  return Bits;
}

SMTExprRef SMTSolverImpl::mkIEEEFPToBV(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  // Bit-exact where provenance is known: if this term was built from bits
  // (or an asserted equality ties it to one that was), hand the original
  // bits back instead of asking the backend — fp.to_ieee_bv is
  // underspecified at NaN and a backend may otherwise answer with any NaN
  // pattern. See IEEEBVShadow. Terms with no provable provenance fall
  // back to the underspecified operation SILENTLY; callers that need
  // unconditional bit-exactness must use FPEncoding::BV.
  if (auto It = IEEEBVShadow.find(&*Exp); It != IEEEBVShadow.end())
    return It->second;
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkIEEEFPToBVImpl(Exp)
                          : mkIEEEFPToBVImpl(Exp);
  // Exactly a plain BV sort: isBVSort() also answers true for BVFP, and a
  // BVFP-sorted result would leak into caller sort comparisons.
  assert(theExp->Sort->getSortKind() == SMTSortKind::BV);
  assert(theExp->getWidth() == Exp->getWidth());
  return theExp;
}

checkResult SMTSolverImpl::check() {
  invalidateUnsatAssumptions();
  return checkImpl();
}

checkResult
SMTSolverImpl::checkSatAssuming(const std::vector<SMTExprRef> &Assumptions) {
  for (const SMTExprRef &Assumption : Assumptions)
    requireBoolSort(Assumption, "Expected boolean assumption");
  // checkSatAssumingImpl may route through the public
  // addConstraint/push/pop (the default fallback and the activation-literal
  // lowerings do), all of which invalidate the unsat-assumption state, so
  // record it only after the check completes.
  const checkResult Result =
      Assumptions.empty() ? checkImpl() : checkSatAssumingImpl(Assumptions);
  UnsatAssumptionsValid = Result == checkResult::UNSAT;
  LastAssumptions =
      UnsatAssumptionsValid ? Assumptions : std::vector<SMTExprRef>{};
  return Result;
}

checkResult SMTSolverImpl::checkSatAssumingImpl(
    const std::vector<SMTExprRef> &Assumptions) {
  push();
  for (const SMTExprRef &Assumption : Assumptions)
    addConstraint(Assumption);
  const checkResult Result = checkImpl();
  pop();
  return Result;
}

SMTResult<std::vector<SMTExprRef>> SMTSolverImpl::getUnsatAssumptions() {
  if (!UnsatAssumptionsValid)
    return SMTError{SMTErrorCode::InvalidUsage,
                    CachedBoolExprs[0]->getBackendKind(),
                    "getUnsatAssumptions is only valid right after a "
                    "checkSatAssuming call that returned UNSAT, before the "
                    "solver state is mutated or checked again"};
  if (LastAssumptions.empty())
    return std::vector<SMTExprRef>{};
  SMTResult<std::vector<SMTExprRef>> Core = getUnsatAssumptionsImpl();
  if (!Core)
    return Core;
  // Normalize across backends: a duplicated assumption must not yield a
  // duplicated core entry (activation-literal lowerings mint one literal
  // per position, so their raw cores can repeat an expression).
  std::vector<SMTExprRef> Deduped;
  for (SMTExprRef &Assumption : Core.value()) {
    bool Seen = false;
    for (const SMTExprRef &Kept : Deduped)
      if (&*Kept == &*Assumption) {
        Seen = true;
        break;
      }
    if (!Seen)
      Deduped.push_back(std::move(Assumption));
  }
  return Deduped;
}

SMTResult<std::vector<SMTExprRef>> SMTSolverImpl::getUnsatAssumptionsImpl() {
  return SMTError{SMTErrorCode::UnsupportedOperation,
                  CachedBoolExprs[0]->getBackendKind(),
                  "Unsat assumptions are not supported by this backend"};
}

// One hook per feature, so the enum and the hooks stay in step: a new
// SolverFeature without a case here is a compile error rather than a
// silent false.
bool SMTSolverImpl::supports(SolverFeature Feature) const {
  switch (Feature) {
  case SolverFeature::IntRealArithmetic:
    return intRealArithmeticSupport();
  case SolverFeature::Quantifiers:
    return quantifierSupport();
  case SolverFeature::UninterpretedFunctions:
    return uninterpretedFunctionSupport();
  case SolverFeature::NativeFloatingPoint:
    return nativeFloatingPointSupport();
  case SolverFeature::NativeTuples:
    return nativeDatatypeSupport();
  case SolverFeature::NativeConstantArrays:
    return nativeConstArraySupport();
  case SolverFeature::UnsatAssumptions:
    return unsatAssumptionSupport();
  case SolverFeature::Timeouts:
    return timeoutSupport();
  case SolverFeature::ArrayModels:
    return arrayModelSupport();
  }
  fatalError("Unhandled SolverFeature in supports()");
}

bool SMTSolverImpl::setTimeout(uint64_t Milliseconds) {
  const bool Supported = setTimeoutImpl(Milliseconds);
  TimeoutMs = Supported ? Milliseconds : 0;
  return Supported;
}

bool SMTSolverImpl::setTimeoutImpl(uint64_t) { return false; }

void SMTSolverImpl::reset() {
  invalidateGeneratedObjects();
  resetImpl();
  initializeCommonSingletons();
  // resetImpl() may recreate the backend context, dropping any limit
  // configured on the old one; the limit itself is solver configuration
  // and survives the reset.
  if (TimeoutMs)
    setTimeoutImpl(TimeoutMs);
}

void SMTSolverImpl::push(unsigned nscopes) {
  invalidateUnsatAssumptions();
  LazyConstraintLevels.resize(LazyConstraintLevels.size() + nscopes);
  ShadowScopeLevels.resize(ShadowScopeLevels.size() + nscopes);
  pushImpl(nscopes);
}

void SMTSolverImpl::pop(unsigned nscopes) {
  invalidateUnsatAssumptions();
  // Lazy default axioms and extensionality lemmas asserted inside the
  // popped scopes are scope-independent facts about expressions that
  // outlive the pop, so re-assert them at the outer level instead of
  // forgetting them.
  std::vector<SMTExprRef> Reassert;
  for (unsigned I = 0; I < nscopes && LazyConstraintLevels.size() > 1; ++I) {
    auto &Level = LazyConstraintLevels.back();
    Reassert.insert(Reassert.end(), std::make_move_iterator(Level.begin()),
                    std::make_move_iterator(Level.end()));
    LazyConstraintLevels.pop_back();
  }
  // Assert-derived bit-pattern shadows die with their scope: the tying
  // equality is retracted by the pop, and keeping the bits without it
  // would let mkIEEEFPToBV claim facts no longer asserted.
  for (unsigned I = 0; I < nscopes && ShadowScopeLevels.size() > 1; ++I) {
    for (const SMTExpr *Key : ShadowScopeLevels.back())
      IEEEBVShadow.erase(Key);
    ShadowScopeLevels.pop_back();
  }
  popImpl(nscopes);
  for (SMTExprRef &Constraint : Reassert) {
    addConstraint(Constraint);
    LazyConstraintLevels.back().push_back(std::move(Constraint));
  }
}

CAMADA_DEFINE_DUMP_TO_STDERR(dump)

void SMTSolverImpl::dump(std::string &Out) { return dumpImpl(Out); }

CAMADA_DEFINE_DUMP_TO_STDERR(dumpModel)

void SMTSolverImpl::dumpModel(std::string &Out) { return dumpModelImpl(Out); }

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTSortRef, mkTupleSortImpl, "Tuples",
                               const std::vector<SMTSortRef> &)

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkBVNorImpl,
                                  mkBVNotImpl(mkBVOrImpl(LHS, RHS)), BVNor)

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkBVUgtImpl, mkNotImpl(mkBVUleImpl(LHS, RHS)),
                                  BVUgt)

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkBVSgtImpl, mkNotImpl(mkBVSleImpl(LHS, RHS)),
                                  BVSgt)

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkBVUgeImpl, mkNotImpl(mkBVUltImpl(LHS, RHS)),
                                  BVUge)

CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkBVSgeImpl, mkNotImpl(mkBVSltImpl(LHS, RHS)),
                                  BVSge)

SMTExprRef SMTSolverImpl::mkBVAddOverflowImpl(const SMTExprRef &LHS,
                                              const SMTExprRef &RHS,
                                              bool IsSigned) {
  const unsigned Width = LHS->getWidth();
  SMTExprRef theExp;
  if (IsSigned) {
    // Signed addition overflows iff the operands have the same sign and the
    // sum's sign differs from it.
    SMTExprRef Sum = mkBVAdd(LHS, RHS);
    SMTExprRef LSign = mkBVExtract(Width - 1, Width - 1, LHS);
    SMTExprRef RSign = mkBVExtract(Width - 1, Width - 1, RHS);
    SMTExprRef SumSign = mkBVExtract(Width - 1, Width - 1, Sum);
    theExp = mkAnd(mkEqual(LSign, RSign), mkNot(mkEqual(LSign, SumSign)));
  } else {
    // Unsigned addition overflows iff the (Width+1)-bit sum carries out.
    SMTExprRef Sum = mkBVAdd(mkBVZeroExt(1, LHS), mkBVZeroExt(1, RHS));
    theExp = mkEqual(mkBVExtract(Width, Width, Sum), getBVOne1Expr());
  }
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVAddOverflow);
}

SMTExprRef SMTSolverImpl::mkBVSubOverflowImpl(const SMTExprRef &LHS,
                                              const SMTExprRef &RHS,
                                              bool IsSigned) {
  const unsigned Width = LHS->getWidth();
  SMTExprRef theExp;
  if (IsSigned) {
    // Signed subtraction overflows iff the operands have different signs and
    // the difference's sign differs from the minuend's.
    SMTExprRef Diff = mkBVSub(LHS, RHS);
    SMTExprRef LSign = mkBVExtract(Width - 1, Width - 1, LHS);
    SMTExprRef RSign = mkBVExtract(Width - 1, Width - 1, RHS);
    SMTExprRef DiffSign = mkBVExtract(Width - 1, Width - 1, Diff);
    theExp =
        mkAnd(mkNot(mkEqual(LSign, RSign)), mkNot(mkEqual(LSign, DiffSign)));
  } else {
    // Unsigned subtraction overflows (borrows) iff LHS < RHS.
    theExp = mkBVUlt(LHS, RHS);
  }
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVSubOverflow);
}

SMTExprRef SMTSolverImpl::mkBVMulOverflowImpl(const SMTExprRef &LHS,
                                              const SMTExprRef &RHS,
                                              bool IsSigned) {
  const unsigned Width = LHS->getWidth();
  SMTExprRef theExp;
  if (IsSigned) {
    // Multiply at double width; the product is representable iff its top
    // Width+1 bits all equal the result's sign bit.
    SMTExprRef Prod = mkBVMul(mkBVSignExt(Width, LHS), mkBVSignExt(Width, RHS));
    SMTExprRef Top = mkBVExtract(2 * Width - 1, Width - 1, Prod);
    SMTExprRef Zeros = mkBVFromDec(0, Width + 1);
    SMTExprRef Ones = mkBVNot(Zeros);
    theExp = mkNot(mkOr(mkEqual(Top, Zeros), mkEqual(Top, Ones)));
  } else {
    // Unsigned: any set bit in the product's top half is an overflow.
    SMTExprRef Prod = mkBVMul(mkBVZeroExt(Width, LHS), mkBVZeroExt(Width, RHS));
    SMTExprRef Top = mkBVExtract(2 * Width - 1, Width, Prod);
    theExp = mkNot(mkEqual(Top, mkBVFromDec(0, Width)));
  }
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVMulOverflow);
}

SMTExprRef SMTSolverImpl::mkBVSDivOverflowImpl(const SMTExprRef &LHS,
                                               const SMTExprRef &RHS) {
  // The only signed-division overflow is MIN_INT / -1.
  const unsigned Width = LHS->getWidth();
  SMTExprRef Min = mkBVFromBin("1" + std::string(Width - 1, '0'), Width);
  SMTExprRef NegOne = mkBVFromDec(-1, Width);
  SMTExprRef theExp = mkAnd(mkEqual(LHS, Min), mkEqual(RHS, NegOne));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVSDivOverflow);
}

SMTExprRef SMTSolverImpl::mkBVNegOverflowImpl(const SMTExprRef &Exp) {
  // Signed negation overflows only for MIN_INT.
  const unsigned Width = Exp->getWidth();
  SMTExprRef Min = mkBVFromBin("1" + std::string(Width - 1, '0'), Width);
  SMTExprRef theExp = mkEqual(Exp, Min);
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVNegOverflow);
}

SMTExprRef SMTSolverImpl::mkXorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  SMTExprRef theExp =
      mkAndImpl(mkOrImpl(LHS, RHS), mkNotImpl(mkAndImpl(LHS, RHS)));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::Xor);
}

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithNegImpl, "Arithmetic",
                               const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithAddImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithSubImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithMulImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithDivImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithModImpl, "Integer arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

SMTExprRef SMTSolverImpl::mkArithShlImpl(const SMTExprRef &Exp,
                                         unsigned Amount) {
  SMTExprRef TheExp = mkArithMulImpl(Exp, mkInt(power2Dec(Amount)));
  return rewrapExprImpl(*TheExp, TheExp->Sort, SMTExprKind::ArithShl);
}

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithShlImpl, "Integer arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithLtImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithGtImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithLeImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkArithGeImpl, "Arithmetic",
                               const SMTExprRef &, const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkInt2RealImpl, "Real arithmetic",
                               const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkReal2IntImpl, "Integer arithmetic",
                               const SMTExprRef &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkIsIntImpl, "Integer arithmetic",
                               const SMTExprRef &)

SMTExprRef SMTSolverImpl::mkBV2IntImpl(const SMTExprRef &Exp, bool IsSigned) {
  // No native conversion: compose the integer as a sum of bit-tests,
  // Sum ite(bit_i = 1, 2^i, 0), minus 2^W when signed and the sign bit is
  // set. Pure Int+BV+ite, so it works on any backend with both theories
  // and over the SMT-LIB pipe.
  const unsigned Width = Exp->getWidth();
  SMTExprRef BitSet = mkBVFromDec(1, 1);
  SMTExprRef Zero = mkInt(0);
  SMTExprRef Sum = Zero;
  for (unsigned I = 0; I < Width; ++I) {
    SMTExprRef Bit = mkBVExtract(I, I, Exp);
    Sum =
        mkArithAdd(Sum, mkIte(mkEqual(Bit, BitSet), mkInt(power2Dec(I)), Zero));
  }
  if (IsSigned) {
    SMTExprRef Sign = mkBVExtract(Width - 1, Width - 1, Exp);
    Sum = mkArithSub(
        Sum, mkIte(mkEqual(Sign, BitSet), mkInt(power2Dec(Width)), Zero));
  }
  return rewrapExprImpl(*Sum, Sum->Sort, SMTExprKind::BV2Int);
}

SMTExprRef SMTSolverImpl::mkInt2BVImpl(unsigned Width, const SMTExprRef &Exp) {
  // No native conversion and no portable operator to compose one from: a
  // bit-vector value tied to an integer can only be introduced through a
  // fresh symbol constrained via the inverse direction (the mkIEEEFPToBV
  // precedent). Euclidean mod puts the wrap in [0, 2^Width) for negative
  // integers too. The constraint is asserted at the current push level
  // and unwound by (pop) — unlike mkIEEEFPToBV's tie, which is journalled
  // into LazyConstraintLevels and re-asserted afterwards.
  SMTExprRef Fresh = mkSymbolUnchecked(
      "__CAMADA_int2bv_" + std::to_string(NextInt2BVId++), mkBVSort(Width));
  SMTExprRef Wrapped = mkArithMod(Exp, mkInt(power2Dec(Width)));
  addConstraint(mkEqual(mkBV2IntImpl(Fresh, /*IsSigned=*/false), Wrapped));
  return rewrapExprImpl(*Fresh, Fresh->Sort, SMTExprKind::Int2BV);
}

SMTExprRef SMTSolverImpl::mkBVRedOrImpl(const SMTExprRef &Exp) {
  // bvredor = bvnot(bvcomp(x,0)) ? bv1 : bv0;
  SMTExprRef comp = mkEqualImpl(Exp, mkBVFromDec(0, Exp->getWidth()));
  SMTExprRef theExp =
      mkIteImpl(mkNotImpl(comp), CachedBVOne1Expr, CachedSmallBVZeroExprs[1]);
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVRedOr);
}

SMTExprRef SMTSolverImpl::mkBVRedAndImpl(const SMTExprRef &Exp) {
  // bvredand = bvcomp(x,-1) ? bv1 : bv0;
  SMTExprRef comp = mkEqualImpl(Exp, mkBVFromDec(-1, Exp->getWidth()));
  SMTExprRef theExp =
      mkIteImpl(comp, CachedBVOne1Expr, CachedSmallBVZeroExprs[1]);
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVRedAnd);
}

// Reversed operands: (a > b) iff (b < a).
CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkFPGtImpl,
                                  SMTSolverImpl::mkFPLtImpl(RHS, LHS), FPGt)

// Reversed operands: (a > b) iff (b < a).
CAMADA_DEFINE_DERIVED_BINARY_IMPL(mkFPGeImpl,
                                  SMTSolverImpl::mkFPLeImpl(RHS, LHS), FPGe)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkTupleImpl, "Tuples",
                               const std::vector<SMTExprRef> &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkTupleSelectImpl, "Tuples",
                               const SMTExprRef &, unsigned)

SMTResult<std::string> SMTSolverImpl::getIntImpl(const SMTExprRef &Exp) {
  return SMTError{SMTErrorCode::UnsupportedOperation, Exp->getBackendKind(),
                  "Integer arithmetic is not supported by this backend"};
}

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkIntImpl, "Integer arithmetic",
                               int64_t)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkIntImpl, "Integer arithmetic",
                               const std::string &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkRealImpl, "Real arithmetic",
                               const std::string &)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkRealImpl, "Real arithmetic",
                               int64_t)

CAMADA_DEFINE_UNSUPPORTED_IMPL(SMTExprRef, mkRealImpl, "Real arithmetic",
                               int64_t, int64_t)

CAMADA_DEFINE_DUMP_TO_STDERR(dumpImpl)

void SMTSolverImpl::dumpImpl(std::string &Out) {
  Out = "SMTSolver dump not implemented.\n";
}

CAMADA_DEFINE_DUMP_TO_STDERR(dumpModelImpl)

void SMTSolverImpl::dumpModelImpl(std::string &Out) {
  Out = "SMTSolver model dump not implemented.\n";
}

} // namespace camada
