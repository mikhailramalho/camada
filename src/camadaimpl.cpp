#include "camadaimpl.h"

#include <cstdio>

namespace camada {

namespace {

std::string addLeadingZeroes(const std::string &Str, const unsigned Width) {
  if (Str.length() == Width)
    return Str;
  return std::string(Width - Str.length(), '0') + Str;
}

} // namespace

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
  assert(BitWidth);
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
  SMTSortRef &CachedSort =
      Encoding == FPEncoding::BV ? CachedEncodedRMSort : CachedNativeRMSort;
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
  assert(ExpWidth && SigWidth);
  auto &Cache =
      Encoding == FPEncoding::BV ? EncodedFPSortCache : NativeFPSortCache;
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
  assert(!DomainSorts.empty());
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
  assert(!ElementSorts.empty());
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

void SMTSolverImpl::addConstraint(const SMTExprRef &Exp) {
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
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVAddImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSub,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVSubImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVMul,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVMulImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSRem,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVSRemImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVURem,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVURemImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSDiv,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVSDivImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUDiv,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVUDivImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVShl,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVShlImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVAshr,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVAshrImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVLshr,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVLshrImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVXor,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVXorImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVOr, assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVOrImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVAnd,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVAndImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVXnor,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVXnorImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVNor,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVNorImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVNand,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVNandImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUlt,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVUltImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSlt,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVSltImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUgt,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVUgtImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSgt,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVSgtImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUle,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVUleImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSle,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVSleImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVUge,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVUgeImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkBVSge,
                                    assert(LHS->isBVSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkBVSgeImpl(LHS, RHS),
                                    assert(theExp->Sort->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkEqual,
                                    assert(LHS->Sort == RHS->Sort),
                                    mkEqualImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkImplies,
                                    assert(LHS->isBoolSort());
                                    assert(*LHS->Sort == *RHS->Sort),
                                    mkImpliesImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkAnd,
                                    assert(LHS->isBoolSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkAndImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkOr, assert(LHS->isBoolSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkOrImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkXor,
                                    assert(LHS->isBoolSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkXorImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithAdd,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithAddImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithSub,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithSubImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithMul,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithMulImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithDiv,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithDivImpl(LHS, RHS),
                                    assert(theExp->Sort == LHS->Sort))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithMod,
                                    assert(LHS->isIntSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithModImpl(LHS, RHS),
                                    assert(theExp->isIntSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithLt,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithLtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithGt,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithGtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithLe,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithLeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkArithGe,
                                    assert(LHS->isArithSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    mkArithGeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPLt, assert(LHS->isFPSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPLtImpl(LHS, RHS)
                                        : mkFPLtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPGt, assert(LHS->isFPSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPGtImpl(LHS, RHS)
                                        : mkFPGtImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPLe, assert(LHS->isFPSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPLeImpl(LHS, RHS)
                                        : mkFPLeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPGe, assert(LHS->isFPSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPGeImpl(LHS, RHS)
                                        : mkFPGeImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))
CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER(SMTExprRef, mkFPEqual,
                                    assert(LHS->isFPSort());
                                    assert(LHS->Sort == RHS->Sort),
                                    usesBVFPEncoding(LHS)
                                        ? SMTSolverImpl::mkFPEqualImpl(LHS, RHS)
                                        : mkFPEqualImpl(LHS, RHS),
                                    assert(theExp->isBoolSort()))

#undef CAMADA_DEFINE_SIMPLE_BINARY_WRAPPER

SMTExprRef SMTSolverImpl::mkBVNeg(const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  SMTExprRef theExp = mkBVNegImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVNot(const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  SMTExprRef theExp = mkBVNotImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkNot(const SMTExprRef &Exp) {
  assert(Exp->isBoolSort());
  SMTExprRef theExp = mkNotImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArithNeg(const SMTExprRef &Exp) {
  assert(Exp->isArithSort());
  SMTExprRef theExp = mkArithNegImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArithShl(const SMTExprRef &Exp, unsigned Amount) {
  assert(Exp->isIntSort());
  SMTExprRef theExp = mkArithShlImpl(Exp, Amount);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArithShl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  assert(LHS->isIntSort());
  assert(RHS->isIntSort());
  SMTExprRef theExp = mkArithShlImpl(LHS, RHS);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkInt2Real(const SMTExprRef &Exp) {
  assert(Exp->isIntSort());
  SMTExprRef theExp = mkInt2RealImpl(Exp);
  assert(theExp->isRealSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkReal2Int(const SMTExprRef &Exp) {
  assert(Exp->isArithSort());
  SMTExprRef theExp = mkReal2IntImpl(Exp);
  assert(theExp->isIntSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIsInt(const SMTExprRef &Exp) {
  assert(Exp->isArithSort());
  SMTExprRef theExp = mkIsIntImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                                const SMTExprRef &F) {
  assert(Cond->isBoolSort());
  assert(T->Sort == F->Sort);
  SMTExprRef theExp = mkIteImpl(Cond, T, F);
  assert(theExp->Sort == F->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  SMTExprRef theExp = mkBVSignExtImpl(i, Exp);
  assert(theExp->getWidth() == Exp->getWidth() + i);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  SMTExprRef theExp = mkBVZeroExtImpl(i, Exp);
  assert(theExp->getWidth() == Exp->getWidth() + i);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVExtract(unsigned High, unsigned Low,
                                      const SMTExprRef &Exp) {
  assert(High >= Low);
  assert(High <= Exp->getWidth());
  assert(Low <= Exp->getWidth());
  SMTExprRef theExp = Exp->isBVSort()
                          ? mkBVExtractImpl(High, Low, Exp)
                          : mkBVExtractImpl(High, Low, mkIEEEFPToBV(Exp));
  assert(theExp->getWidth() == (High - Low + 1));
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVConcat(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  assert(LHS->isBVSort());
  assert(RHS->isBVSort());
  SMTExprRef theExp = mkBVConcatImpl(LHS, RHS);
  assert(theExp->getWidth() == (LHS->getWidth() + RHS->getWidth()));
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVRedOr(const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  SMTExprRef theExp = mkBVRedOrImpl(Exp);
  assert(theExp->getWidth() == 1);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkBVRedAnd(const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  SMTExprRef theExp = mkBVRedAndImpl(Exp);
  assert(theExp->getWidth() == 1);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPAbs(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPAbsImpl(Exp)
                                            : mkFPAbsImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPNeg(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPNegImpl(Exp)
                                            : mkFPNegImpl(Exp);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsInfinite(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPIsInfiniteImpl(Exp)
                          : mkFPIsInfiniteImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsNaN(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPIsNaNImpl(Exp)
                                            : mkFPIsNaNImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsDenormal(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPIsDenormalImpl(Exp)
                          : mkFPIsDenormalImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsNormal(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPIsNormalImpl(Exp)
                          : mkFPIsNormalImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPIsZero(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPIsZeroImpl(Exp)
                                            : mkFPIsZeroImpl(Exp);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  assert(LHS->isFPSort());
  assert(LHS->Sort == RHS->Sort);
  assert(R->isRMSort());
  assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPMulImpl(LHS, RHS, R)
                          : mkFPMulImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  assert(LHS->isFPSort());
  assert(LHS->Sort == RHS->Sort);
  assert(R->isRMSort());
  assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPDivImpl(LHS, RHS, R)
                          : mkFPDivImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPRem(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  assert(LHS->isFPSort());
  assert(LHS->Sort == RHS->Sort);
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPRemImpl(LHS, RHS)
                          : mkFPRemImpl(LHS, RHS);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  assert(LHS->isFPSort());
  assert(LHS->Sort == RHS->Sort);
  assert(R->isRMSort());
  assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPAddImpl(LHS, RHS, R)
                          : mkFPAddImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const SMTExprRef &R) {
  assert(LHS->isFPSort());
  assert(LHS->Sort == RHS->Sort);
  assert(R->isRMSort());
  assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(LHS)
                          ? SMTSolverImpl::mkFPSubImpl(LHS, RHS, R)
                          : mkFPSubImpl(LHS, RHS, R);
  assert(theExp->Sort == LHS->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPSqrt(const SMTExprRef &Exp, const SMTExprRef &R) {
  assert(Exp->isFPSort());
  assert(R->isRMSort());
  assert(usesBVFPEncoding(Exp) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(Exp)
                          ? SMTSolverImpl::mkFPSqrtImpl(Exp, R)
                          : mkFPSqrtImpl(Exp, R);
  assert(theExp->Sort == Exp->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                                  const SMTExprRef &Z, const SMTExprRef &R) {
  assert(X->isFPSort());
  assert(X->Sort == Y->Sort);
  assert(Y->Sort == Z->Sort);
  assert(R->isRMSort());
  assert(usesBVFPEncoding(X) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(X)
                          ? SMTSolverImpl::mkFPFMAImpl(X, Y, Z, R)
                          : mkFPFMAImpl(X, Y, Z, R);
  assert(theExp->Sort == Z->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R) {
  assert(From->isFPSort());
  assert(To->isFPSort());
  assert(R->isRMSort());
  assert(usesBVFPEncoding(From) == usesBVFPEncoding(To));
  assert(usesBVFPEncoding(To) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkFPtoFPImpl(From, To, R)
                          : mkFPtoFPImpl(From, To, R);
  assert(theExp->Sort == To);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkSBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To, const SMTExprRef &R) {
  assert(From->isBVSort());
  assert(To->isFPSort());
  assert(R->isRMSort());
  assert(usesBVFPEncoding(To) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkSBVtoFPImpl(From, To, R)
                          : mkSBVtoFPImpl(From, To, R);
  assert(theExp->Sort == To);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkUBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To, const SMTExprRef &R) {
  assert(From->isBVSort());
  assert(To->isFPSort());
  assert(R->isRMSort());
  assert(usesBVFPEncoding(To) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkUBVtoFPImpl(From, To, R)
                          : mkUBVtoFPImpl(From, To, R);
  assert(theExp->Sort == To);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  assert(From->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(From)
                          ? SMTSolverImpl::mkFPtoSBVImpl(From, ToWidth)
                          : mkFPtoSBVImpl(From, ToWidth);
  assert(theExp->getWidth() == ToWidth);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  assert(From->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(From)
                          ? SMTSolverImpl::mkFPtoUBVImpl(From, ToWidth)
                          : mkFPtoUBVImpl(From, ToWidth);
  assert(theExp->getWidth() == ToWidth);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkFPtoIntegral(const SMTExprRef &From,
                                         const SMTExprRef &R) {
  assert(From->isFPSort());
  assert(R->isRMSort());
  assert(usesBVFPEncoding(From) == usesBVRMEncoding(R));
  SMTExprRef theExp = usesBVFPEncoding(From)
                          ? SMTSolverImpl::mkFPtoIntegralImpl(From, R)
                          : mkFPtoIntegralImpl(From, R);
  assert(theExp->isFPSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArraySelect(const SMTExprRef &Array,
                                        const SMTExprRef &Index) {
  assert(Array->isArraySort());
  assert(Array->Sort->getIndexSort() == Index->Sort);
  SMTExprRef theExp = mkArraySelectImpl(Array, Index);
  assert(theExp->Sort == Array->Sort->getElementSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkArrayStore(const SMTExprRef &Array,
                                       const SMTExprRef &Index,
                                       const SMTExprRef &Element) {
  assert(Array->isArraySort());
  assert(Array->Sort->getIndexSort() == Index->Sort);
  assert(Array->Sort->getElementSort() == Element->Sort);
  SMTExprRef theExp = mkArrayStoreImpl(Array, Index, Element);
  assert(theExp->Sort == Array->Sort);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkTuple(const std::vector<SMTExprRef> &Elements) {
  assert(!Elements.empty());
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
  assert(Tuple->Sort->isTupleSort());
  assert(Index < Tuple->Sort->getTupleElementSorts().size());
  SMTExprRef theExp = mkTupleSelectImpl(Tuple, Index);
  assert(theExp->Sort == Tuple->Sort->getTupleElementSorts()[Index]);
  return theExp;
}

SMTExprRef SMTSolverImpl::mkApply(const SMTExprRef &Function,
                                  const std::vector<SMTExprRef> &Args) {
  assert(Function->isFunctionSort());
  assert(Function->Sort->getDomainSorts().size() == Args.size());
  for (std::size_t i = 0; i < Args.size(); ++i)
    assert(Function->Sort->getDomainSorts()[i] == Args[i]->Sort);
  SMTExprRef theExp = mkApplyImpl(Function, Args);
  assert(theExp->Sort == Function->Sort->getCodomainSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkForall(const std::vector<SMTExprRef> &Vars,
                                   const SMTExprRef &Body) {
  assert(Body->isBoolSort());
  SMTExprRef theExp = mkForallImpl(Vars, Body);
  assert(theExp->isBoolSort());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkExists(const std::vector<SMTExprRef> &Vars,
                                   const SMTExprRef &Body) {
  assert(Body->isBoolSort());
  SMTExprRef theExp = mkExistsImpl(Vars, Body);
  assert(theExp->isBoolSort());
  return theExp;
}

bool SMTSolverImpl::getBool(const SMTExprRef &Exp) {
  assert(Exp->isBoolSort());
  return getBoolImpl(Exp);
}

int64_t SMTSolverImpl::getBV(const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  return getBVImpl(Exp);
}

std::string SMTSolverImpl::getBVInBin(const SMTExprRef &Exp) {
  assert(Exp->isBVSort());
  return addLeadingZeroes(getBVInBinImpl(Exp), Exp->getWidth());
}

std::string SMTSolverImpl::getInt(const SMTExprRef &Exp) {
  assert(Exp->isIntSort() || Exp->isRealSort());
  return getIntImpl(Exp);
}

void SMTSolverImpl::getRational(const SMTExprRef &Exp, std::string &Num,
                                std::string &Den) {
  assert(Exp->isRealSort());
  getRationalImpl(Exp, Num, Den);
}

std::string SMTSolverImpl::getRealNumerator(const SMTExprRef &Exp) {
  assert(Exp->isRealSort());
  std::string Num, Den;
  getRationalImpl(Exp, Num, Den);
  return Num;
}

std::string SMTSolverImpl::getRealDenominator(const SMTExprRef &Exp) {
  assert(Exp->isRealSort());
  std::string Num, Den;
  getRationalImpl(Exp, Num, Den);
  return Den;
}

std::string SMTSolverImpl::getFPInBin(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  return addLeadingZeroes(usesBVFPEncoding(Exp)
                              ? SMTSolverImpl::getFPInBinImpl(Exp)
                              : getFPInBinImpl(Exp),
                          Exp->getWidth());
}

float SMTSolverImpl::getFP32(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  return getFP32Impl(Exp);
}

double SMTSolverImpl::getFP64(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
  return getFP64Impl(Exp);
}

SMTExprRef SMTSolverImpl::getArrayElement(const SMTExprRef &Array,
                                          const SMTExprRef &Index) {
  assert(Array->isArraySort());
  assert(Array->Sort->getIndexSort() == Index->Sort);
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
  assert(Sort->isBVSort());
  if (Sort->getSortKind() == SMTSortKind::BV) {
    const unsigned Width = Sort->getWidth();
    if (Int == 0 && Width < CachedSmallBVZeroExprs.size())
      return CachedSmallBVZeroExprs[Width];
    if (Int == 1 && Width == 1)
      return CachedBVOne1Expr;
  }

  if (Sort->getSortKind() == SMTSortKind::BV && Int >= -1 && Int <= 1) {
    std::vector<SMTExprRef> *Cache = nullptr;
    switch (Int) {
    case -1:
      Cache = &CachedBVNegOneExprs;
      break;
    case 0:
      Cache = &CachedBVZeroExprs;
      break;
    case 1:
      Cache = &CachedBVOneExprs;
      break;
    default:
      break;
    }

    assert(Cache);
    if (Cache->size() <= Sort->getWidth())
      Cache->resize(Sort->getWidth() + 1);

    SMTExprRef &CachedExpr = (*Cache)[Sort->getWidth()];
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
  assert(Sort->isBVSort());
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
  SMTSortRef Sort = mkFPSort(EWidth, FP.length() - EWidth - 1, Encoding);
  SMTExprRef theExp = usesBVFPEncoding(Sort)
                          ? SMTSolverImpl::mkFPFromBinImpl(FP, EWidth)
                          : mkFPFromBinImpl(FP, EWidth);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == FP.length());
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
  assert(SigWidth);
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
  assert(SigWidth);
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
  assert(Exp->isBVSort() && To->isFPSort());
  SMTExprRef theExp = usesBVFPEncoding(To)
                          ? SMTSolverImpl::mkBVToIEEEFPImpl(Exp, To)
                          : mkBVToIEEEFPImpl(Exp, To);
  assert(theExp->isFPSort());
  assert(theExp->getWidth() == Exp->getWidth());
  return theExp;
}

SMTExprRef SMTSolverImpl::mkIEEEFPToBV(const SMTExprRef &Exp) {
  assert(Exp->isFPSort());
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

} // namespace camada
