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
#include "camadaerror.h"
#include "camadafp.h"

#include <cstdio>
#include <limits>

namespace camada {

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
  ArraySortCache.clear();
  SmallFunctionSortCache.clear();
  FunctionSortCache.clear();
  SmallTupleSortCache.clear();
  TupleSortCache.clear();
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

SMTSortRef SMTSolverImpl::mkBoolSort() {
  if (CachedBoolSort)
    return CachedBoolSort;

  SMTSortRef theSort = mkBoolSortImpl();
  assert(theSort->isBoolSort());
  CachedBoolSort = theSort;
  return theSort;
}

SMTSortRef SMTSolverImpl::mkIntSort() {
  if (CachedIntSort)
    return CachedIntSort;

  SMTSortRef theSort = mkIntSortImpl();
  assert(theSort->isIntSort());
  CachedIntSort = theSort;
  return theSort;
}

SMTSortRef SMTSolverImpl::mkRealSort() {
  if (CachedRealSort)
    return CachedRealSort;

  SMTSortRef theSort = mkRealSortImpl();
  assert(theSort->isRealSort());
  CachedRealSort = theSort;
  return theSort;
}

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
  ArraySortCacheKey Key{IndexSort.get(), ElemSort.get()};
  auto It = ArraySortCache.find(Key);
  if (It != ArraySortCache.end())
    return It->second;

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
  if (ElementSorts.size() <= 4) {
    SmallTupleSortCacheKey SmallKey{};
    SmallKey.Size = static_cast<uint8_t>(ElementSorts.size());
    for (uint8_t I = 0; I < SmallKey.Size; ++I)
      SmallKey.ElementSorts[I] = ElementSorts[I].get();

    auto It = SmallTupleSortCache.find(SmallKey);
    if (It != SmallTupleSortCache.end())
      return It->second;

    SMTSortRef theSort = mkTupleSortImpl(ElementSorts);
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

  SMTSortRef theSort = mkTupleSortImpl(ElementSorts);
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
  return addConstraintImpl(Exp);
}

#define CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(ReturnType, Name, SortAssert,      \
                                            ImplCall, ResultAssert)            \
  ReturnType SMTSolverImpl::Name(const SMTExprRef &LHS,                        \
                                 const SMTExprRef &RHS) {                      \
    SortAssert;                                                                \
    SMTExprRef theExp = ImplCall;                                              \
    ResultAssert;                                                              \
    return theExp;                                                             \
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
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(
    SMTExprRef, mkEqual,
    requireSameSort(LHS, RHS, "Expected expressions with same sort"),
    mkEqualImpl(LHS, RHS), assert(theExp->isBoolSort()))
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

SMTExprRef SMTSolverImpl::mkBVXnorImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  SMTExprRef theExp = mkBVNotImpl(mkBVXorImpl(LHS, RHS));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVXnor);
}

SMTExprRef SMTSolverImpl::mkBVNandImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  SMTExprRef theExp = mkBVNotImpl(mkBVAndImpl(LHS, RHS));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVNand);
}

SMTExprRef SMTSolverImpl::mkImpliesImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  // This is: logical-or(logical-not(LHS), RHS)
  SMTExprRef theExp = mkOrImpl(mkNotImpl(LHS), RHS);
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::Implies);
}

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

SMTExprRef SMTSolverImpl::mkBVNeg(const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  SMTExprRef theExp = mkBVNegImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVNot(const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  SMTExprRef theExp = mkBVNotImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkNot(const SMTExprRef &Exp) {
  requireBoolSort(Exp, "Expected boolean expression");
  SMTExprRef theExp = mkNotImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArithNeg(const SMTExprRef &Exp) {
  requireArithSort(Exp, "Expected arithmetic expression");
  SMTExprRef theExp = mkArithNegImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

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

SMTExprRef SMTSolverImpl::mkInt2Real(const SMTExprRef &Exp) {
  requireIntSort(Exp, "Expected integer expression");
  SMTExprRef theExp = mkInt2RealImpl(Exp);
  assert(theExp->isRealSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkReal2Int(const SMTExprRef &Exp) {
  requireArithSort(Exp, "Expected arithmetic expression");
  SMTExprRef theExp = mkReal2IntImpl(Exp);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIsInt(const SMTExprRef &Exp) {
  requireArithSort(Exp, "Expected arithmetic expression");
  SMTExprRef theExp = mkIsIntImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                                const SMTExprRef &F) {
  requireBoolSort(Cond, "Expected boolean condition");
  requireSameSort(T, F, "Expected ITE branches with same sort");
  SMTExprRef theExp = mkIteImpl(Cond, T, F);
  assert(theExp->Sort == F->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  fatalErrorIf(i > std::numeric_limits<unsigned>::max() - Exp->getWidth(),
               "Bit-vector sign extension width overflow");
  SMTExprRef theExp = mkBVSignExtImpl(i, Exp);
  assert(theExp->getWidth() == Exp->getWidth() + i);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  fatalErrorIf(i > std::numeric_limits<unsigned>::max() - Exp->getWidth(),
               "Bit-vector zero extension width overflow");
  SMTExprRef theExp = mkBVZeroExtImpl(i, Exp);
  assert(theExp->getWidth() == Exp->getWidth() + i);
  return theExp;
}

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

SMTExprRef SMTSolverImpl::mkBVRedOr(const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  SMTExprRef theExp = mkBVRedOrImpl(Exp);
  assert(theExp->getWidth() == 1);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVRedAnd(const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  SMTExprRef theExp = mkBVRedAndImpl(Exp);
  assert(theExp->getWidth() == 1);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPAbs(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPAbsImpl(Exp)
                                            : mkFPAbsImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPNeg(const SMTExprRef &Exp,
                                  FPNegBehavior Behavior) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPNegImpl(Exp, Behavior)
                          : mkFPNegImpl(Exp, Behavior);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsInfinite(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPIsInfiniteImpl(Exp)
                          : mkFPIsInfiniteImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsNaN(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPIsNaNImpl(Exp)
                                            : mkFPIsNaNImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsDenormal(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPIsDenormalImpl(Exp)
                          : mkFPIsDenormalImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsNormal(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPIsNormalImpl(Exp)
                          : mkFPIsNormalImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsZero(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPIsZeroImpl(Exp)
                                            : mkFPIsZeroImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  requireFPSameSortAndRM(LHS, RHS, R);
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPMulImpl(LHS, RHS, R)
                          : mkFPMulImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  requireFPSameSortAndRM(LHS, RHS, R);
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPDivImpl(LHS, RHS, R)
                          : mkFPDivImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPRem(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  requireFPSameSort(LHS, RHS);
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPRemImpl(LHS, RHS)
                          : mkFPRemImpl(LHS, RHS);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  requireFPSameSortAndRM(LHS, RHS, R);
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPAddImpl(LHS, RHS, R)
                          : mkFPAddImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  requireFPSameSortAndRM(LHS, RHS, R);
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPSubImpl(LHS, RHS, R)
                          : mkFPSubImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

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

SMTExprRef SMTSolverImpl::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  requireFPSort(From, "Expected floating-point expression");
  fatalErrorIf(ToWidth == 0, "Bit-vector target width must be non-zero");
  SMTExprRef theExp = usesBVFPEncoding(From)
                          ? SMTSolverImpl::mkFPtoSBVImpl(From, ToWidth)
                          : mkFPtoSBVImpl(From, ToWidth);
  assert(theExp->getWidth() == ToWidth);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  requireFPSort(From, "Expected floating-point expression");
  fatalErrorIf(ToWidth == 0, "Bit-vector target width must be non-zero");
  SMTExprRef theExp = usesBVFPEncoding(From)
                          ? SMTSolverImpl::mkFPtoUBVImpl(From, ToWidth)
                          : mkFPtoUBVImpl(From, ToWidth);
  assert(theExp->getWidth() == ToWidth);
  return theExp;
}

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
  SMTExprRef theExp = mkArrayStoreImpl(Array, Index, Element);
  assert(theExp->Sort == Array->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkTuple(const std::vector<SMTExprRef> &Elements) {
  std::vector<SMTSortRef> ElementSorts;
  ElementSorts.reserve(Elements.size());
  for (const auto &Element : Elements)
    ElementSorts.push_back(Element->Sort);
  SMTSortRef TupleSort = mkTupleSort(ElementSorts);
  SMTExprRef theExp = mkTupleImpl(Elements);
  assert(theExp->Sort == TupleSort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkTupleSelect(const SMTExprRef &Tuple,
                                        unsigned Index) {
  fatalErrorIf(!Tuple->Sort->isTupleSort(), "Expected tuple expression");
  fatalErrorIf(Index >= Tuple->Sort->getTupleElementSorts().size(),
               "Tuple element index is out of bounds");
  SMTExprRef theExp = mkTupleSelectImpl(Tuple, Index);
  assert(theExp->Sort == Tuple->Sort->getTupleElementSorts()[Index]);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkApply(const SMTExprRef &Function,
                                  const std::vector<SMTExprRef> &Args) {
  fatalErrorIf(!Function->isFunctionSort(), "Expected function expression");
  fatalErrorIf(Function->Sort->getDomainSorts().size() != Args.size(),
               "Function application argument count mismatch");
  for (std::size_t i = 0; i < Args.size(); ++i)
    fatalErrorIf(Function->Sort->getDomainSorts()[i] != Args[i]->Sort,
                 "Function application argument sort mismatch");
  SMTExprRef theExp = mkApplyImpl(Function, Args);
  assert(theExp->Sort == Function->Sort->getCodomainSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkApplyImpl(const SMTExprRef &,
                                      const std::vector<SMTExprRef> &) {
  unsupportedFeature("Uninterpreted functions");
}

SMTExprRef SMTSolverImpl::mkForall(const std::vector<SMTExprRef> &Vars,
                                   const SMTExprRef &Body) {
  requireBoolSort(Body, "Expected boolean quantifier body");
  SMTExprRef theExp = mkForallImpl(Vars, Body);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkForallImpl(const std::vector<SMTExprRef> &,
                                       const SMTExprRef &) {
  unsupportedFeature("Quantifiers");
}

SMTExprRef SMTSolverImpl::mkExists(const std::vector<SMTExprRef> &Vars,
                                   const SMTExprRef &Body) {
  requireBoolSort(Body, "Expected boolean quantifier body");
  SMTExprRef theExp = mkExistsImpl(Vars, Body);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkExistsImpl(const std::vector<SMTExprRef> &,
                                       const SMTExprRef &) {
  unsupportedFeature("Quantifiers");
}

SMTResult<bool> SMTSolverImpl::getBool(const SMTExprRef &Exp) {
  requireBoolSort(Exp, "Expected boolean expression");
  return getBoolImpl(Exp);
}

SMTResult<int64_t> SMTSolverImpl::getBV(const SMTExprRef &Exp) {
  requireBVSort(Exp, "Expected bit-vector expression");
  return getBVImpl(Exp);
}

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

SMTResult<float> SMTSolverImpl::getFP32(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  return getFP32Impl(Exp);
}

SMTResult<double> SMTSolverImpl::getFP64(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  return getFP64Impl(Exp);
}

SMTExprRef SMTSolverImpl::getArrayElement(const SMTExprRef &Array,
                                          const SMTExprRef &Index) {
  fatalErrorIf(!Array->isArraySort(), "Expected array expression");
  fatalErrorIf(Array->Sort->getIndexSort() != Index->Sort,
               "Expected array index with matching sort");
  SMTExprRef theExp = getArrayElementImpl(Array, Index);
  assert(theExp->Sort == Array->Sort->getElementSort());
  return theExp;
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

SMTExprRef SMTSolverImpl::mkInt(int64_t v) {
  SMTExprRef theExp = mkIntImpl(v);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkInt(const std::string &v) {
  SMTExprRef theExp = mkIntImpl(v);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkReal(const std::string &v) {
  SMTExprRef theExp = mkRealImpl(v);
  assert(theExp->isRealSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkReal(int64_t v) {
  SMTExprRef theExp = mkRealImpl(v);
  assert(theExp->isRealSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkReal(int64_t num, int64_t den) {
  SMTExprRef theExp = mkRealImpl(num, den);
  assert(theExp->isRealSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVFromDec(const int64_t Int,
                                      const SMTSortRef &Sort) {
  fatalErrorIf(!Sort->isBVSort(),
               "Bit-vector decimal literal sort must be bit-vector");
  if (Sort->getSortKind() == SMTSortKind::BV) {
    const unsigned Width = Sort->getWidth();
    if (Int == 0 && Width < CachedSmallBVZeroExprs.size())
      return CachedSmallBVZeroExprs[Width];
    if (Int == 1 && Width == 1)
      return CachedBVOne1Expr;
  }

  if (Sort->getSortKind() == SMTSortKind::BV && Int >= -1 && Int <= 1) {
    auto &Cache = CachedSmallBVExprs[cachedSmallBVExprIndex(Int)];
    if (Cache.size() <= Sort->getWidth())
      Cache.resize(Sort->getWidth() + 1);

    SMTExprRef &CachedExpr = Cache[Sort->getWidth()];
    if (CachedExpr)
      return CachedExpr;

    SMTExprRef theExp = mkBVFromDecImpl(Int, Sort);
    assert(theExp->isBVSort());
    assert(theExp->getWidth() == Sort->getWidth());
    CachedExpr = theExp;
    return CachedExpr;
  }

  SMTExprRef theExp = mkBVFromDecImpl(Int, Sort);
  assert(theExp->isBVSort());
  assert(theExp->getWidth() == Sort->getWidth());
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
  SymbolExprCacheKey Key{Sort.get(), Name};
  auto Cached = SymbolExprCache.find(Key);
  if (Cached != SymbolExprCache.end())
    return Cached->second;

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
  FPConstExprCache.emplace(std::move(Key), theExp);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFP32(const float Float, FPEncoding Encoding) {
  SMTExprRef theExp = mkFP32Impl(Float, Encoding);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == 32);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFP64(const double Double, FPEncoding Encoding) {
  SMTExprRef theExp = mkFP64Impl(Double, Encoding);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == 64);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkRM(const RM &R, FPEncoding Encoding) {
  SMTExprRef theExp =
      Encoding == FPEncoding::BV ? SMTSolverImpl::mkRMImpl(R) : mkRMImpl(R);
  assert(theExp->isRMSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkNaN(const bool Sgn, const unsigned ExpWidth,
                                const unsigned SigWidth, FPEncoding Encoding) {
  fatalErrorIf(SigWidth == 0,
               "Floating-point significand width must be non-zero");
  SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, Encoding);
  SMTExprRef theExp = usesBVFPEncoding(Sort)
                          ? SMTSolverImpl::mkNaNImpl(Sgn, ExpWidth, SigWidth)
                          : mkNaNImpl(Sgn, ExpWidth, SigWidth);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == (ExpWidth + SigWidth));
  assert(theExp->getWidth() == theExp->Sort->getWidthFromSolver());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkNaN32(const bool Sgn, FPEncoding Encoding) {
  return mkNaN(Sgn, 8, 24, Encoding);
}

SMTExprRef SMTSolverImpl::mkNaN64(const bool Sgn, FPEncoding Encoding) {
  return mkNaN(Sgn, 11, 53, Encoding);
}

SMTExprRef SMTSolverImpl::mkInf(const bool Sgn, const unsigned ExpWidth,
                                const unsigned SigWidth, FPEncoding Encoding) {
  fatalErrorIf(SigWidth == 0,
               "Floating-point significand width must be non-zero");
  SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, Encoding);
  SMTExprRef theExp = usesBVFPEncoding(Sort)
                          ? SMTSolverImpl::mkInfImpl(Sgn, ExpWidth, SigWidth)
                          : mkInfImpl(Sgn, ExpWidth, SigWidth);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == (ExpWidth + SigWidth));
  assert(theExp->getWidth() == theExp->Sort->getWidthFromSolver());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkInf32(const bool Sgn, FPEncoding Encoding) {
  return mkInf(Sgn, 8, 24, Encoding);
}

SMTExprRef SMTSolverImpl::mkInf64(const bool Sgn, FPEncoding Encoding) {
  return mkInf(Sgn, 11, 53, Encoding);
}

SMTExprRef SMTSolverImpl::mkArrayConst(const SMTSortRef &IndexSort,
                                       const SMTExprRef &InitValue) {
  SMTExprRef theExp = mkArrayConstImpl(IndexSort, InitValue);
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
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIEEEFPToBV(const SMTExprRef &Exp) {
  requireFPSort(Exp, "Expected floating-point expression");
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkIEEEFPToBVImpl(Exp)
                          : mkIEEEFPToBVImpl(Exp);
  assert(theExp->isBVSort());
  assert(theExp->getWidth() == Exp->getWidth());
  return theExp;
}

checkResult SMTSolverImpl::check() { return checkImpl(); }

void SMTSolverImpl::reset() {
  invalidateGeneratedObjects();
  resetImpl();
  initializeCommonSingletons();
}

void SMTSolverImpl::push(unsigned nscopes) { pushImpl(nscopes); }

void SMTSolverImpl::pop(unsigned nscopes) { popImpl(nscopes); }

void SMTSolverImpl::dump() {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSolverImpl::dump(std::string &Out) { return dumpImpl(Out); }

void SMTSolverImpl::dumpModel() {
  std::string Out;
  dumpModel(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSolverImpl::dumpModel(std::string &Out) { return dumpModelImpl(Out); }

SMTSortRef SMTSolverImpl::mkTupleSortImpl(const std::vector<SMTSortRef> &) {
  unsupportedFeature("Tuples");
}

SMTExprRef SMTSolverImpl::mkBVNorImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  SMTExprRef theExp = mkBVNotImpl(mkBVOrImpl(LHS, RHS));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVNor);
}

SMTExprRef SMTSolverImpl::mkBVUgtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  SMTExprRef theExp = mkNotImpl(mkBVUleImpl(LHS, RHS));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVUgt);
}

SMTExprRef SMTSolverImpl::mkBVSgtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  SMTExprRef theExp = mkNotImpl(mkBVSleImpl(LHS, RHS));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVSgt);
}

SMTExprRef SMTSolverImpl::mkBVUgeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  SMTExprRef theExp = mkNotImpl(mkBVUltImpl(LHS, RHS));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVUge);
}

SMTExprRef SMTSolverImpl::mkBVSgeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  SMTExprRef theExp = mkNotImpl(mkBVSltImpl(LHS, RHS));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::BVSge);
}

SMTExprRef SMTSolverImpl::mkXorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  SMTExprRef theExp =
      mkAndImpl(mkOrImpl(LHS, RHS), mkNotImpl(mkAndImpl(LHS, RHS)));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::Xor);
}

SMTExprRef SMTSolverImpl::mkArithNegImpl(const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithAddImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithSubImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithMulImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithDivImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithModImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeature("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithShlImpl(const SMTExprRef &Exp,
                                         unsigned Amount) {
  SMTExprRef TheExp = mkArithMulImpl(Exp, mkInt(power2Dec(Amount)));
  return rewrapExprImpl(*TheExp, TheExp->Sort, SMTExprKind::ArithShl);
}

SMTExprRef SMTSolverImpl::mkArithShlImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeature("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithLtImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithGtImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithLeImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithGeImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeature("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkInt2RealImpl(const SMTExprRef &) {
  unsupportedFeature("Real arithmetic");
}

SMTExprRef SMTSolverImpl::mkReal2IntImpl(const SMTExprRef &) {
  unsupportedFeature("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkIsIntImpl(const SMTExprRef &) {
  unsupportedFeature("Integer arithmetic");
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

SMTExprRef SMTSolverImpl::mkFPGtImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  SMTExprRef theExp = SMTSolverImpl::mkFPLtImpl(RHS, LHS);
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::FPGt);
}

SMTExprRef SMTSolverImpl::mkFPGeImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  // (a >= b) iff (b <= a)
  SMTExprRef theExp = SMTSolverImpl::mkFPLeImpl(RHS, LHS);
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::FPGe);
}

SMTExprRef SMTSolverImpl::mkTupleImpl(const std::vector<SMTExprRef> &) {
  unsupportedFeature("Tuples");
}

SMTExprRef SMTSolverImpl::mkTupleSelectImpl(const SMTExprRef &, unsigned) {
  unsupportedFeature("Tuples");
}

SMTResult<std::string> SMTSolverImpl::getIntImpl(const SMTExprRef &Exp) {
  return SMTError{SMTErrorCode::UnsupportedOperation, Exp->getBackendKind(),
                  "Integer arithmetic is not supported by this backend"};
}

SMTExprRef SMTSolverImpl::mkIntImpl(int64_t) {
  unsupportedFeature("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkIntImpl(const std::string &) {
  unsupportedFeature("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkRealImpl(const std::string &) {
  unsupportedFeature("Real arithmetic");
}

SMTExprRef SMTSolverImpl::mkRealImpl(int64_t) {
  unsupportedFeature("Real arithmetic");
}

SMTExprRef SMTSolverImpl::mkRealImpl(int64_t, int64_t) {
  unsupportedFeature("Real arithmetic");
}

void SMTSolverImpl::dumpImpl() {
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSolverImpl::dumpImpl(std::string &Out) {
  Out = "SMTSolver dump not implemented.\n";
}

void SMTSolverImpl::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSolverImpl::dumpModelImpl(std::string &Out) {
  Out = "SMTSolver model dump not implemented.\n";
}

} // namespace camada
