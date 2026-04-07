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

#ifndef CAMADAIMPL_H_
#define CAMADAIMPL_H_

#include "camada.h"

#include <cassert>
#include <cstdio>
#include <string>

namespace camada {

class SMTSolverImpl : public SMTSolver {
public:
  SMTSolverImpl() = default;
  virtual ~SMTSolverImpl() override = default;

  SMTExprRef getBVZero1Expr() const { return CachedSmallBVZeroExprs[1]; }
  SMTExprRef getBVOne1Expr() const { return CachedBVOne1Expr; }
  SMTExprRef getBVZero2Expr() const { return CachedSmallBVZeroExprs[2]; }
  SMTExprRef getBVZero3Expr() const { return CachedSmallBVZeroExprs[3]; }
  SMTExprRef getBVZero4Expr() const { return CachedSmallBVZeroExprs[4]; }
  SMTExprRef getRMExpr(RM R) const {
    return CachedRMBVExprs[static_cast<std::size_t>(R)];
  }
  SMTExprRef getFPSpecialExpr(unsigned ExpWidth, unsigned SigWidth,
                              FPSpecialValueKind Kind, bool Sign);

  static SMTExprRef tagExprKind(const SMTExprRef &Exp, SMTExprKind Kind) {
    const_cast<SMTExpr &>(*Exp).setKind(Kind);
    return Exp;
  }

  static bool usesBVFPEncoding(const SMTSortRef &Sort) {
    return Sort->isBVFPSort();
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

protected:
  /// Wrapper to create new SMTSort
  template <typename SolverSort>
  SMTSortRef newSortRef(const SolverSort &Sort) const {
    auto OwnedSort = std::make_unique<SolverSort>(Sort);
#ifndef NDEBUG
    assert(OwnedSort->validateSortWidth());
    OwnedSort->markWidthValidated();
#endif
    const SMTSort *SortPtr = OwnedSort.get();
    SortArena.emplace_back(std::move(OwnedSort));
    return SMTSortRef(SortPtr, HandleState, HandleState->Generation);
  }

  template <typename SolverExpr>
  SMTExprRef storeExprRef(const SolverExpr &Exp) const {
    auto OwnedExpr = std::make_unique<SolverExpr>(Exp);
    const SMTExpr *ExprPtr = OwnedExpr.get();
    ExprArena.emplace_back(std::move(OwnedExpr));
    return SMTExprRef(ExprPtr, HandleState, HandleState->Generation);
  }

  template <typename SolverExpr>
  SMTExprRef storeOwnedExprRef(std::unique_ptr<SolverExpr> Exp) const {
    const SMTExpr *ExprPtr = Exp.get();
    ExprArena.emplace_back(std::move(Exp));
    return SMTExprRef(ExprPtr, HandleState, HandleState->Generation);
  }

  void invalidateGeneratedObjects();

  void clearSortCaches();

  void clearExprCaches();

  void initializeCommonSingletons();

  mutable std::deque<std::unique_ptr<SMTSort>> SortArena;
  mutable std::deque<std::unique_ptr<SMTExpr>> ExprArena;
  mutable std::array<SMTExprRef, 2> CachedBoolExprs;
  mutable SMTExprRef CachedBVOne1Expr;
  mutable std::array<SMTExprRef, 5> CachedSmallBVZeroExprs;
  mutable std::array<SMTExprRef, 5> CachedRMBVExprs;
  mutable std::vector<SMTExprRef> CachedBVNegOneExprs;
  mutable std::vector<SMTExprRef> CachedBVZeroExprs;
  mutable std::vector<SMTExprRef> CachedBVOneExprs;
  mutable SMTSortRef CachedBoolSort;
  mutable SMTSortRef CachedIntSort;
  mutable SMTSortRef CachedRealSort;
  mutable SMTSortRef CachedNativeRMSort;
  mutable SMTSortRef CachedEncodedRMSort;
  mutable std::unordered_map<SymbolExprCacheKey, SMTExprRef,
                             SymbolExprCacheKeyHash>
      SymbolExprCache;
  mutable std::unordered_map<FPSpecialExprCacheKey, SMTExprRef,
                             FPSpecialExprCacheKeyHash>
      FPSpecialExprCache;
  mutable std::unordered_map<unsigned, SMTSortRef> BVSortCache;
  mutable std::unordered_map<FPSortCacheKey, SMTSortRef, FPSortCacheKeyHash>
      NativeFPSortCache;
  mutable std::unordered_map<FPSortCacheKey, SMTSortRef, FPSortCacheKeyHash>
      EncodedFPSortCache;
  mutable std::unordered_map<ArraySortCacheKey, SMTSortRef,
                             ArraySortCacheKeyHash>
      ArraySortCache;
  mutable std::unordered_map<FunctionSortCacheKey, SMTSortRef,
                             FunctionSortCacheKeyHash>
      FunctionSortCache;
  std::shared_ptr<SMTHandleState> HandleState =
      std::make_shared<SMTHandleState>();

protected:
  SMTExprRef newExprRef(const SMTExpr &Exp) const {
    SMTExprRef theExp = newExprRefImpl(Exp);
#ifndef NDEBUG
    assert(theExp->Sort->isWidthValidated());
#endif
    return theExp;
  }

public:
  SMTSortRef mkBoolSort() override final {
    if (CachedBoolSort)
      return CachedBoolSort;

    SMTSortRef theSort = mkBoolSortImpl();
    assert(theSort->isBoolSort());
    CachedBoolSort = theSort;
    return theSort;
  }

  SMTSortRef mkIntSort() override final {
    if (CachedIntSort)
      return CachedIntSort;

    SMTSortRef theSort = mkIntSortImpl();
    assert(theSort->isIntSort());
    CachedIntSort = theSort;
    return theSort;
  }

  SMTSortRef mkRealSort() override final {
    if (CachedRealSort)
      return CachedRealSort;

    SMTSortRef theSort = mkRealSortImpl();
    assert(theSort->isRealSort());
    CachedRealSort = theSort;
    return theSort;
  }

  SMTSortRef mkBVSort(const unsigned BitWidth) override final {
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

  SMTSortRef mkRMSort(FPEncoding Encoding) override final {
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

  SMTSortRef mkFPSort(const unsigned ExpWidth, const unsigned SigWidth,
                      FPEncoding Encoding) override final {
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

  SMTSortRef mkFP32Sort(FPEncoding Encoding) override final {
    return mkFPSort(8, 23, Encoding);
  }

  SMTSortRef mkFP64Sort(FPEncoding Encoding) override final {
    return mkFPSort(11, 52, Encoding);
  }

  SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                         const SMTSortRef &ElemSort) override final {
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

  SMTSortRef mkFunctionSort(const std::vector<SMTSortRef> &DomainSorts,
                            const SMTSortRef &CodomainSort) override final {
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

  void addConstraint(const SMTExprRef &Exp) override final {
    return addConstraintImpl(Exp);
  }

  SMTExprRef mkBVAdd(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVAddImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVAdd);
  }

  SMTExprRef mkBVSub(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVSubImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVSub);
  }

  SMTExprRef mkBVMul(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVMulImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVMul);
  }

  SMTExprRef mkBVSRem(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVSRemImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVSRem);
  }

  SMTExprRef mkBVURem(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVURemImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVURem);
  }

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVSDivImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVSDiv);
  }

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVUDivImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVUDiv);
  }

  SMTExprRef mkBVShl(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVShlImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVShl);
  }

  SMTExprRef mkBVAshr(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVAshrImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVAshr);
  }

  SMTExprRef mkBVLshr(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVLshrImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVLshr);
  }

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    SMTExprRef theExp = mkBVNegImpl(Exp);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::BVNeg);
  }

  SMTExprRef mkBVNot(const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    SMTExprRef theExp = mkBVNotImpl(Exp);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::BVNot);
  }

  SMTExprRef mkBVXor(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVXorImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVXor);
  }

  SMTExprRef mkBVOr(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVOrImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVOr);
  }

  SMTExprRef mkBVAnd(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVAndImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVAnd);
  }

  SMTExprRef mkBVXnor(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVXnorImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVXnor);
  }

  SMTExprRef mkBVNor(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVNorImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVNor);
  }

  SMTExprRef mkBVNand(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVNandImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::BVNand);
  }

  SMTExprRef mkBVUlt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVUltImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVUlt);
  }

  SMTExprRef mkBVSlt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVSltImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVSlt);
  }

  SMTExprRef mkBVUgt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVUgtImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVUgt);
  }

  SMTExprRef mkBVSgt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVSgtImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVSgt);
  }

  SMTExprRef mkBVUle(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVUleImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVUle);
  }

  SMTExprRef mkBVSle(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVSleImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVSle);
  }

  SMTExprRef mkBVUge(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVUgeImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVUge);
  }

  SMTExprRef mkBVSge(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkBVSgeImpl(LHS, RHS);
    assert(theExp->Sort->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::BVSge);
  }

  SMTExprRef mkNot(const SMTExprRef &Exp) override final {
    assert(Exp->isBoolSort());
    SMTExprRef theExp = mkNotImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::Not);
  }

  SMTExprRef mkEqual(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkEqualImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::Equal);
  }

  SMTExprRef mkImplies(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final {
    assert(LHS->isBoolSort());
    assert(*LHS->Sort == *RHS->Sort);
    SMTExprRef theExp = mkImpliesImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::Implies);
  }

  SMTExprRef mkAnd(const SMTExprRef &LHS,
                   const SMTExprRef &RHS) override final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkAndImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::And);
  }

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkOrImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::Or);
  }

  SMTExprRef mkXor(const SMTExprRef &LHS,
                   const SMTExprRef &RHS) override final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkXorImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::Xor);
  }

  SMTExprRef mkArithNeg(const SMTExprRef &Exp) override final {
    assert(Exp->isArithSort());
    SMTExprRef theExp = mkArithNegImpl(Exp);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::ArithNeg);
  }

  SMTExprRef mkArithAdd(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithAddImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::ArithAdd);
  }

  SMTExprRef mkArithSub(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithSubImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::ArithSub);
  }

  SMTExprRef mkArithMul(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithMulImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::ArithMul);
  }

  SMTExprRef mkArithDiv(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithDivImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::ArithDiv);
  }

  SMTExprRef mkArithMod(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final {
    assert(LHS->isIntSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithModImpl(LHS, RHS);
    assert(theExp->isIntSort());
    return tagExprKind(theExp, SMTExprKind::ArithMod);
  }

  SMTExprRef mkArithShl(const SMTExprRef &Exp, unsigned Amount) override final {
    assert(Exp->isIntSort());
    SMTExprRef theExp = mkArithShlImpl(Exp, Amount);
    assert(theExp->isIntSort());
    return tagExprKind(theExp, SMTExprKind::ArithShl);
  }

  SMTExprRef mkArithShl(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final {
    assert(LHS->isIntSort());
    assert(RHS->isIntSort());
    SMTExprRef theExp = mkArithShlImpl(LHS, RHS);
    assert(theExp->isIntSort());
    return tagExprKind(theExp, SMTExprKind::ArithShl);
  }

  SMTExprRef mkArithLt(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithLtImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::ArithLt);
  }

  SMTExprRef mkArithGt(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithGtImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::ArithGt);
  }

  SMTExprRef mkArithLe(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithLeImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::ArithLe);
  }

  SMTExprRef mkArithGe(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final {
    assert(LHS->isArithSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = mkArithGeImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::ArithGe);
  }

  SMTExprRef mkInt2Real(const SMTExprRef &Exp) override final {
    assert(Exp->isIntSort());
    SMTExprRef theExp = mkInt2RealImpl(Exp);
    assert(theExp->isRealSort());
    return tagExprKind(theExp, SMTExprKind::Int2Real);
  }

  SMTExprRef mkReal2Int(const SMTExprRef &Exp) override final {
    assert(Exp->isArithSort());
    SMTExprRef theExp = mkReal2IntImpl(Exp);
    assert(theExp->isIntSort());
    return tagExprKind(theExp, SMTExprKind::Real2Int);
  }

  SMTExprRef mkIsInt(const SMTExprRef &Exp) override final {
    assert(Exp->isArithSort());
    SMTExprRef theExp = mkIsIntImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::IsInt);
  }

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) override final {
    assert(Cond->isBoolSort());
    assert(T->Sort == F->Sort);
    SMTExprRef theExp = mkIteImpl(Cond, T, F);
    assert(theExp->Sort == F->Sort);
    return tagExprKind(theExp, SMTExprKind::Ite);
  }

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    SMTExprRef theExp = mkBVSignExtImpl(i, Exp);
    assert(theExp->getWidth() == Exp->getWidth() + i);
    return tagExprKind(theExp, SMTExprKind::BVSignExt);
  }

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    SMTExprRef theExp = mkBVZeroExtImpl(i, Exp);
    assert(theExp->getWidth() == Exp->getWidth() + i);
    return tagExprKind(theExp, SMTExprKind::BVZeroExt);
  }

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) override final {
    assert(High >= Low);
    assert(High <= Exp->getWidth());
    assert(Low <= Exp->getWidth());
    SMTExprRef theExp = Exp->isBVSort()
                            ? mkBVExtractImpl(High, Low, Exp)
                            : mkBVExtractImpl(High, Low, mkIEEEFPToBV(Exp));
    assert(theExp->getWidth() == (High - Low + 1));
    return tagExprKind(theExp, SMTExprKind::BVExtract);
  }

  SMTExprRef mkBVConcat(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final {
    assert(LHS->isBVSort());
    assert(RHS->isBVSort());
    SMTExprRef theExp = mkBVConcatImpl(LHS, RHS);
    assert(theExp->getWidth() == (LHS->getWidth() + RHS->getWidth()));
    return tagExprKind(theExp, SMTExprKind::BVConcat);
  }

  SMTExprRef mkBVRedOr(const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    SMTExprRef theExp = mkBVRedOrImpl(Exp);
    assert(theExp->getWidth() == 1);
    return tagExprKind(theExp, SMTExprKind::BVRedOr);
  }

  SMTExprRef mkBVRedAnd(const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    SMTExprRef theExp = mkBVRedAndImpl(Exp);
    assert(theExp->getWidth() == 1);
    return tagExprKind(theExp, SMTExprKind::BVRedAnd);
  }

  SMTExprRef mkFPAbs(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPAbsImpl(Exp)
                                              : mkFPAbsImpl(Exp);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::FPAbs);
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp) ? SMTSolverImpl::mkFPNegImpl(Exp)
                                              : mkFPNegImpl(Exp);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::FPNeg);
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp)
                            ? SMTSolverImpl::mkFPIsInfiniteImpl(Exp)
                            : mkFPIsInfiniteImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsInfinite);
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp)
                            ? SMTSolverImpl::mkFPIsNaNImpl(Exp)
                            : mkFPIsNaNImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsNaN);
  }

  SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp)
                            ? SMTSolverImpl::mkFPIsDenormalImpl(Exp)
                            : mkFPIsDenormalImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsDenormal);
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp)
                            ? SMTSolverImpl::mkFPIsNormalImpl(Exp)
                            : mkFPIsNormalImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsNormal);
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp)
                            ? SMTSolverImpl::mkFPIsZeroImpl(Exp)
                            : mkFPIsZeroImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsZero);
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    assert(R->isRMSort());
    assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPMulImpl(LHS, RHS, R)
                            : mkFPMulImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPMul);
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    assert(R->isRMSort());
    assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPDivImpl(LHS, RHS, R)
                            : mkFPDivImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPDiv);
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPRemImpl(LHS, RHS)
                            : mkFPRemImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPRem);
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    assert(R->isRMSort());
    assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPAddImpl(LHS, RHS, R)
                            : mkFPAddImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPAdd);
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    assert(R->isRMSort());
    assert(usesBVFPEncoding(LHS) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPSubImpl(LHS, RHS, R)
                            : mkFPSubImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPSub);
  }

  SMTExprRef mkFPSqrt(const SMTExprRef &Exp,
                      const SMTExprRef &R) override final {
    assert(Exp->isFPSort());
    assert(R->isRMSort());
    assert(usesBVFPEncoding(Exp) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(Exp)
                            ? SMTSolverImpl::mkFPSqrtImpl(Exp, R)
                            : mkFPSqrtImpl(Exp, R);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::FPSqrt);
  }

  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const SMTExprRef &R) override final {
    assert(X->isFPSort());
    assert(X->Sort == Y->Sort);
    assert(Y->Sort == Z->Sort);
    assert(R->isRMSort());
    assert(usesBVFPEncoding(X) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(X)
                            ? SMTSolverImpl::mkFPFMAImpl(X, Y, Z, R)
                            : mkFPFMAImpl(X, Y, Z, R);
    assert(theExp->Sort == Z->Sort);
    return tagExprKind(theExp, SMTExprKind::FPFMA);
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPLtImpl(LHS, RHS)
                            : mkFPLtImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPLt);
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPGtImpl(LHS, RHS)
                            : mkFPGtImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPGt);
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPLeImpl(LHS, RHS)
                            : mkFPLeImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPLe);
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPGeImpl(LHS, RHS)
                            : mkFPGeImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPGe);
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = usesBVFPEncoding(LHS)
                            ? SMTSolverImpl::mkFPEqualImpl(LHS, RHS)
                            : mkFPEqualImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPEqual);
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const SMTExprRef &R) override final {
    assert(From->isFPSort());
    assert(To->isFPSort());
    assert(R->isRMSort());
    assert(usesBVFPEncoding(From) == usesBVFPEncoding(To));
    assert(usesBVFPEncoding(To) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(To)
                            ? SMTSolverImpl::mkFPtoFPImpl(From, To, R)
                            : mkFPtoFPImpl(From, To, R);
    assert(theExp->Sort == To);
    return tagExprKind(theExp, SMTExprKind::FPtoFP);
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const SMTExprRef &R) override final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    assert(R->isRMSort());
    assert(usesBVFPEncoding(To) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(To)
                            ? SMTSolverImpl::mkSBVtoFPImpl(From, To, R)
                            : mkSBVtoFPImpl(From, To, R);
    assert(theExp->Sort == To);
    return tagExprKind(theExp, SMTExprKind::SBVtoFP);
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const SMTExprRef &R) override final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    assert(R->isRMSort());
    assert(usesBVFPEncoding(To) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(To)
                            ? SMTSolverImpl::mkUBVtoFPImpl(From, To, R)
                            : mkUBVtoFPImpl(From, To, R);
    assert(theExp->Sort == To);
    return tagExprKind(theExp, SMTExprKind::UBVtoFP);
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From,
                       unsigned ToWidth) override final {
    assert(From->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(From)
                            ? SMTSolverImpl::mkFPtoSBVImpl(From, ToWidth)
                            : mkFPtoSBVImpl(From, ToWidth);
    assert(theExp->getWidth() == ToWidth);
    return tagExprKind(theExp, SMTExprKind::FPtoSBV);
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From,
                       unsigned ToWidth) override final {
    assert(From->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(From)
                            ? SMTSolverImpl::mkFPtoUBVImpl(From, ToWidth)
                            : mkFPtoUBVImpl(From, ToWidth);
    assert(theExp->getWidth() == ToWidth);
    return tagExprKind(theExp, SMTExprKind::FPtoUBV);
  }

  SMTExprRef mkFPtoIntegral(const SMTExprRef &From,
                            const SMTExprRef &R) override final {
    assert(From->isFPSort());
    assert(R->isRMSort());
    assert(usesBVFPEncoding(From) == usesBVRMEncoding(R));
    SMTExprRef theExp = usesBVFPEncoding(From)
                            ? SMTSolverImpl::mkFPtoIntegralImpl(From, R)
                            : mkFPtoIntegralImpl(From, R);
    assert(theExp->isFPSort());
    return tagExprKind(theExp, SMTExprKind::FPtoIntegral);
  }

  SMTExprRef mkArraySelect(const SMTExprRef &Array,
                           const SMTExprRef &Index) override final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    SMTExprRef theExp = mkArraySelectImpl(Array, Index);
    assert(theExp->Sort == Array->Sort->getElementSort());
    return tagExprKind(theExp, SMTExprKind::ArraySelect);
  }

  SMTExprRef mkArrayStore(const SMTExprRef &Array, const SMTExprRef &Index,
                          const SMTExprRef &Element) override final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    assert(Array->Sort->getElementSort() == Element->Sort);
    SMTExprRef theExp = mkArrayStoreImpl(Array, Index, Element);
    assert(theExp->Sort == Array->Sort);
    return tagExprKind(theExp, SMTExprKind::ArrayStore);
  }

  SMTExprRef mkApply(const SMTExprRef &Function,
                     const std::vector<SMTExprRef> &Args) override final {
    assert(Function->isFunctionSort());
    assert(Function->Sort->getDomainSorts().size() == Args.size());
    for (std::size_t i = 0; i < Args.size(); ++i)
      assert(Function->Sort->getDomainSorts()[i] == Args[i]->Sort);
    SMTExprRef theExp = mkApplyImpl(Function, Args);
    assert(theExp->Sort == Function->Sort->getCodomainSort());
    return tagExprKind(theExp, SMTExprKind::Apply);
  }

  SMTExprRef mkForall(const std::vector<SMTExprRef> &Vars,
                      const SMTExprRef &Body) override final {
    assert(Body->isBoolSort());
    SMTExprRef theExp = mkForallImpl(Vars, Body);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::Forall);
  }

  SMTExprRef mkExists(const std::vector<SMTExprRef> &Vars,
                      const SMTExprRef &Body) override final {
    assert(Body->isBoolSort());
    SMTExprRef theExp = mkExistsImpl(Vars, Body);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::Exists);
  }

  bool getBool(const SMTExprRef &Exp) override final {
    assert(Exp->isBoolSort());
    return getBoolImpl(Exp);
  }

  int64_t getBV(const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    return getBVImpl(Exp);
  }

  static inline const std::string addLeadingZeroes(const std::string &Str,
                                                   const unsigned Width) {
    if (Str.length() == Width)
      return Str;
    return std::string(Width - Str.length(), '0') + Str;
  }

  std::string getBVInBin(const SMTExprRef &Exp) override final {
    assert(Exp->isBVSort());
    return addLeadingZeroes(getBVInBinImpl(Exp), Exp->getWidth());
  }

  std::string getInt(const SMTExprRef &Exp) override final {
    assert(Exp->isIntSort() || Exp->isRealSort());
    return getIntImpl(Exp);
  }

  void getRational(const SMTExprRef &Exp, std::string &Num,
                   std::string &Den) override final {
    assert(Exp->isRealSort());
    getRationalImpl(Exp, Num, Den);
  }

  std::string getRealNumerator(const SMTExprRef &Exp) override final {
    assert(Exp->isRealSort());
    std::string Num, Den;
    getRationalImpl(Exp, Num, Den);
    return Num;
  }

  std::string getRealDenominator(const SMTExprRef &Exp) override final {
    assert(Exp->isRealSort());
    std::string Num, Den;
    getRationalImpl(Exp, Num, Den);
    return Den;
  }

  std::string getFPInBin(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    return addLeadingZeroes(usesBVFPEncoding(Exp)
                                ? SMTSolverImpl::getFPInBinImpl(Exp)
                                : getFPInBinImpl(Exp),
                            Exp->getWidth());
  }

  float getFP32(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    return getFP32Impl(Exp);
  }

  double getFP64(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    return getFP64Impl(Exp);
  }

  SMTExprRef getArrayElement(const SMTExprRef &Array,
                             const SMTExprRef &Index) override final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    SMTExprRef theExp = getArrayElementImpl(Array, Index);
    assert(theExp->Sort == Array->Sort->getElementSort());
    return tagExprKind(theExp, SMTExprKind::ArraySelect);
  }

  SMTExprRef mkBool(const bool b) override final {
    SMTExprRef &CachedExpr = CachedBoolExprs[b ? 1 : 0];
    if (CachedExpr)
      return CachedExpr;

    SMTExprRef theExp = mkBoolImpl(b);
    assert(theExp->isBoolSort());
    CachedExpr = theExp;
    return tagExprKind(CachedExpr, SMTExprKind::BoolConst);
  }

  SMTExprRef mkInt(int64_t v) override final {
    SMTExprRef theExp = mkIntImpl(v);
    assert(theExp->isIntSort());
    return tagExprKind(theExp, SMTExprKind::IntConst);
  }

  SMTExprRef mkInt(const std::string &v) override final {
    SMTExprRef theExp = mkIntImpl(v);
    assert(theExp->isIntSort());
    return tagExprKind(theExp, SMTExprKind::IntConst);
  }

  SMTExprRef mkReal(const std::string &v) override final {
    SMTExprRef theExp = mkRealImpl(v);
    assert(theExp->isRealSort());
    return tagExprKind(theExp, SMTExprKind::RealConst);
  }

  SMTExprRef mkReal(int64_t v) override final {
    SMTExprRef theExp = mkRealImpl(v);
    assert(theExp->isRealSort());
    return tagExprKind(theExp, SMTExprKind::RealConst);
  }

  SMTExprRef mkReal(int64_t num, int64_t den) override final {
    SMTExprRef theExp = mkRealImpl(num, den);
    assert(theExp->isRealSort());
    return tagExprKind(theExp, SMTExprKind::RealConst);
  }

  SMTExprRef mkBVFromDec(const int64_t Int,
                         const SMTSortRef &Sort) override final {
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
      CachedExpr = tagExprKind(theExp, SMTExprKind::BVConst);
      return CachedExpr;
    }

    SMTExprRef theExp = mkBVFromDecImpl(Int, Sort);
    assert(theExp->isBVSort());
    assert(theExp->getWidth() == Sort->getWidth());
    return tagExprKind(theExp, SMTExprKind::BVConst);
  }

  SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) override final {
    return mkBVFromDec(Int, mkBVSort(BitWidth));
  }

  SMTExprRef mkBVFromBin(const std::string &Int,
                         const SMTSortRef &Sort) override final {
    assert(Sort->isBVSort());
    SMTExprRef theExp = mkBVFromBinImpl(Int, Sort);
    assert(theExp->isBVSort());
    assert(theExp->getWidth() == Sort->getWidth());
    return tagExprKind(theExp, SMTExprKind::BVConst);
  }

  SMTExprRef mkBVFromBin(const std::string &Int,
                         unsigned BitWidth) override final {
    return mkBVFromBin(Int, mkBVSort(BitWidth));
  }

  SMTExprRef mkBVFromBin(const std::string &Int) override final {
    return mkBVFromBin(Int, Int.length());
  }

  SMTExprRef mkSymbol(const std::string &Name,
                      const SMTSortRef &Sort) override final {
    SymbolExprCacheKey Key{Sort.get(), Name};
    auto Cached = SymbolExprCache.find(Key);
    if (Cached != SymbolExprCache.end())
      return Cached->second;

    SMTExprRef theExp = mkSymbolImpl(Name, Sort);
    assert(theExp->Sort == Sort);
    SymbolExprCache.emplace(Key, theExp);
    return tagExprKind(theExp, SMTExprKind::Symbol);
  }

  SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth,
                         FPEncoding Encoding) override {
    SMTSortRef Sort = mkFPSort(EWidth, FP.length() - EWidth - 1, Encoding);
    SMTExprRef theExp = usesBVFPEncoding(Sort)
                            ? SMTSolverImpl::mkFPFromBinImpl(FP, EWidth)
                            : mkFPFromBinImpl(FP, EWidth);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == FP.length());
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkFP32(const float Float, FPEncoding Encoding) override final {
    SMTExprRef theExp = mkFP32Impl(Float, Encoding);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == 32);
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkFP64(const double Double, FPEncoding Encoding) override final {
    SMTExprRef theExp = mkFP64Impl(Double, Encoding);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == 64);
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkRM(const RM &R, FPEncoding Encoding) override final {
    SMTExprRef theExp =
        Encoding == FPEncoding::BV ? SMTSolverImpl::mkRMImpl(R) : mkRMImpl(R);
    assert(theExp->isRMSort());
    return tagExprKind(theExp, SMTExprKind::RMConst);
  }

  SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth,
                   FPEncoding Encoding) override final {
    assert(SigWidth);
    SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, Encoding);
    SMTExprRef theExp = usesBVFPEncoding(Sort)
                            ? SMTSolverImpl::mkNaNImpl(Sgn, ExpWidth, SigWidth)
                            : mkNaNImpl(Sgn, ExpWidth, SigWidth);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == (ExpWidth + SigWidth));
    assert(theExp->getWidth() == theExp->Sort->getWidthFromSolver());
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkNaN32(const bool Sgn, FPEncoding Encoding) override final {
    return mkNaN(Sgn, 8, 24, Encoding);
  }

  SMTExprRef mkNaN64(const bool Sgn, FPEncoding Encoding) override final {
    return mkNaN(Sgn, 11, 53, Encoding);
  }

  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth,
                   FPEncoding Encoding) override final {
    assert(SigWidth);
    SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, Encoding);
    SMTExprRef theExp = usesBVFPEncoding(Sort)
                            ? SMTSolverImpl::mkInfImpl(Sgn, ExpWidth, SigWidth)
                            : mkInfImpl(Sgn, ExpWidth, SigWidth);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == (ExpWidth + SigWidth));
    assert(theExp->getWidth() == theExp->Sort->getWidthFromSolver());
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkInf32(const bool Sgn, FPEncoding Encoding) override final {
    return mkInf(Sgn, 8, 24, Encoding);
  }

  SMTExprRef mkInf64(const bool Sgn, FPEncoding Encoding) override final {
    return mkInf(Sgn, 11, 53, Encoding);
  }

  SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                          const SMTExprRef &InitValue) override final {
    SMTExprRef theExp = mkArrayConstImpl(IndexSort, InitValue);
    assert(theExp->isArraySort());
    assert(theExp->Sort->getIndexSort() == IndexSort);
    assert(theExp->Sort->getElementSort() == InitValue->Sort);
    return tagExprKind(theExp, SMTExprKind::ArrayConst);
  }

  SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp,
                          const SMTSortRef &To) override final {
    assert(Exp->isBVSort() && To->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(To)
                            ? SMTSolverImpl::mkBVToIEEEFPImpl(Exp, To)
                            : mkBVToIEEEFPImpl(Exp, To);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == Exp->getWidth());
    return tagExprKind(theExp, SMTExprKind::BVToIEEEFP);
  }

  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = usesBVFPEncoding(Exp)
                            ? SMTSolverImpl::mkIEEEFPToBVImpl(Exp)
                            : mkIEEEFPToBVImpl(Exp);
    assert(theExp->isBVSort());
    assert(theExp->getWidth() == Exp->getWidth());
    return tagExprKind(theExp, SMTExprKind::IEEEFPToBV);
  }

  checkResult check() override final { return checkImpl(); }

  void reset() override final {
    invalidateGeneratedObjects();
    resetImpl();
    initializeCommonSingletons();
  }

  void push(unsigned nscopes = 1) override final { pushImpl(nscopes); }

  void pop(unsigned nscopes = 1) override final { popImpl(nscopes); }

  void dump() override final {
    std::string Out;
    dump(Out);
    std::fprintf(stderr, "%s", Out.c_str());
  }
  void dump(std::string &Out) override final { return dumpImpl(Out); }

  void dumpModel() override final {
    std::string Out;
    dumpModel(Out);
    std::fprintf(stderr, "%s", Out.c_str());
  }
  void dumpModel(std::string &Out) override final { return dumpModelImpl(Out); }

protected:
  [[noreturn]] void unsupportedFeatureImpl(const char *Feature) const;

  virtual SMTExprRef newExprRefImpl(const SMTExpr &Exp) const = 0;

  virtual SMTExprRef cloneExprWithSortImpl(const SMTExpr &Exp,
                                           const SMTSortRef &Sort) const = 0;

  virtual SMTSortRef mkBoolSortImpl() = 0;

  virtual SMTSortRef mkIntSortImpl();

  virtual SMTSortRef mkRealSortImpl();

  virtual SMTSortRef mkBVSortImpl(const unsigned BitWidth) = 0;

  virtual SMTSortRef mkRMSortImpl();

  virtual SMTSortRef mkFPSortImpl(const unsigned ExpWidth,
                                  const unsigned SigWidth);

  virtual SMTSortRef mkArraySortImpl(const SMTSortRef &IndexSort,
                                     const SMTSortRef &ElemSort) = 0;

  virtual SMTSortRef
  mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                     const SMTSortRef &CodomainSort);

  virtual void addConstraintImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVAddImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSubImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVMulImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSRemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVURemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVUDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVShlImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVAshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVLshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVNegImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVNotImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVXorImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVOrImpl(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVAndImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVXnorImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
    return mkBVNot(mkBVXor(LHS, RHS));
  };

  virtual SMTExprRef mkBVNorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkBVNot(mkBVOr(LHS, RHS));
  };

  virtual SMTExprRef mkBVNandImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
    return mkBVNot(mkBVAnd(LHS, RHS));
  };

  virtual SMTExprRef mkBVUltImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSltImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVUgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVUle(LHS, RHS));
  }

  virtual SMTExprRef mkBVSgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVSle(LHS, RHS));
  }

  virtual SMTExprRef mkBVUleImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSleImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVUgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVUlt(LHS, RHS));
  }

  virtual SMTExprRef mkBVSgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVSlt(LHS, RHS));
  }

  virtual SMTExprRef mkNotImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkEqualImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkImpliesImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
    // This is: logical-or(logical-not(LHS), RHS)
    return mkOr(mkNot(LHS), RHS);
  }

  virtual SMTExprRef mkAndImpl(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkAnd(mkOr(LHS, RHS), mkNot(mkAnd(LHS, RHS)));
  }

  virtual SMTExprRef mkArithNegImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkArithAddImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS);

  virtual SMTExprRef mkArithSubImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS);

  virtual SMTExprRef mkArithMulImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS);

  virtual SMTExprRef mkArithDivImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS);

  virtual SMTExprRef mkArithModImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS);

  virtual SMTExprRef mkArithShlImpl(const SMTExprRef &Exp, unsigned Amount);

  virtual SMTExprRef mkArithShlImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS);

  virtual SMTExprRef mkArithLtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkArithGtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkArithLeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkArithGeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkInt2RealImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkReal2IntImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkIsIntImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                               const SMTExprRef &F) = 0;

  virtual SMTExprRef mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVExtractImpl(unsigned High, unsigned Low,
                                     const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVConcatImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVRedOrImpl(const SMTExprRef &Exp) {
    // bvredor = bvnot(bvcomp(x,0)) ? bv1 : bv0;
    SMTExprRef comp = mkEqual(Exp, mkBVFromDec(0, Exp->getWidth()));
    return mkIte(mkNot(comp), CachedBVOne1Expr, CachedSmallBVZeroExprs[1]);
  }

  virtual SMTExprRef mkBVRedAndImpl(const SMTExprRef &Exp) {
    // bvredand = bvcomp(x,-1) ? bv1 : bv0;
    SMTExprRef comp = mkEqual(Exp, mkBVFromDec(-1, Exp->getWidth()));
    return mkIte(comp, CachedBVOne1Expr, CachedSmallBVZeroExprs[1]);
  }

  virtual SMTExprRef mkFPAbsImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPNegImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsInfiniteImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsNaNImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsDenormalImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsNormalImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsZeroImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPSqrtImpl(const SMTExprRef &Exp, const SMTExprRef &R);

  virtual SMTExprRef mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                 const SMTExprRef &Z, const SMTExprRef &R);

  virtual SMTExprRef mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPGtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkFPLt(RHS, LHS);
  }

  virtual SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPGeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    // (a >= b) iff (b <= a)
    return mkFPLe(RHS, LHS);
  }

  virtual SMTExprRef mkFPEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                  const SMTExprRef &R);

  virtual SMTExprRef mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R);

  virtual SMTExprRef mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R);

  virtual SMTExprRef mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoIntegralImpl(const SMTExprRef &From,
                                        const SMTExprRef &R);

  virtual SMTExprRef mkArraySelectImpl(const SMTExprRef &Array,
                                       const SMTExprRef &Index) = 0;

  virtual SMTExprRef mkArrayStoreImpl(const SMTExprRef &Array,
                                      const SMTExprRef &Index,
                                      const SMTExprRef &Element) = 0;

  virtual SMTExprRef mkApplyImpl(const SMTExprRef &Function,
                                 const std::vector<SMTExprRef> &Args);

  virtual SMTExprRef mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                  const SMTExprRef &Body);

  virtual SMTExprRef mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                  const SMTExprRef &Body);

  virtual bool getBoolImpl(const SMTExprRef &Exp) = 0;

  int64_t getBVImpl(const SMTExprRef &Exp);

  virtual std::string getBVInBinImpl(const SMTExprRef &Exp) = 0;

  virtual std::string getIntImpl(const SMTExprRef &Exp);

  virtual void getRationalImpl(const SMTExprRef &Exp, std::string &Num,
                               std::string &Den);

  virtual std::string getFPInBinImpl(const SMTExprRef &Exp);

  float getFP32Impl(const SMTExprRef &Exp);

  double getFP64Impl(const SMTExprRef &Exp);

  virtual SMTExprRef getArrayElementImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) = 0;

  virtual SMTExprRef mkBoolImpl(const bool b) = 0;

  virtual SMTExprRef mkIntImpl(int64_t v);

  virtual SMTExprRef mkIntImpl(const std::string &v);

  virtual SMTExprRef mkRealImpl(const std::string &v);

  virtual SMTExprRef mkRealImpl(int64_t v);

  virtual SMTExprRef mkRealImpl(int64_t num, int64_t den);

  virtual SMTExprRef mkBVFromDecImpl(const int64_t Int,
                                     const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkBVFromBinImpl(const std::string &Int,
                                     const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkSymbolImpl(const std::string &Name,
                                  const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkFPFromBinImpl(const std::string &FP, unsigned EWidth);

  SMTExprRef mkFP32Impl(const float Float, FPEncoding Encoding);

  SMTExprRef mkFP64Impl(const double Double, FPEncoding Encoding);

  virtual SMTExprRef mkRMImpl(const RM &R);

  virtual SMTExprRef mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkArrayConstImpl(const SMTSortRef &IndexSort,
                                      const SMTExprRef &InitValue) = 0;

  virtual SMTExprRef mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                      const SMTSortRef &To);

  virtual SMTExprRef mkIEEEFPToBVImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkToBV(const SMTExprRef &Exp, bool isSigned,
                            unsigned int width);

  virtual SMTExprRef round(const SMTExprRef &R, const SMTExprRef &Sgn,
                           SMTExprRef &Sig, SMTExprRef &Exp, unsigned EWidth,
                           unsigned SWidth);

  virtual checkResult checkImpl() = 0;

  virtual void resetImpl() = 0;

  virtual void pushImpl(unsigned nscopes) = 0;

  virtual void popImpl(unsigned nscopes) = 0;

  virtual void dumpImpl();
  virtual void dumpImpl(std::string &Out);

  virtual void dumpModelImpl();
  virtual void dumpModelImpl(std::string &Out);

  virtual SMTSortRef mkBVFPSortImpl(const unsigned ExpWidth,
                                    const unsigned SigWidth) = 0;

  virtual SMTSortRef mkBVRMSortImpl() = 0;
};

} // namespace camada

#endif
