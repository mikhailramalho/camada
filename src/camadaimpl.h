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
#include <string>

namespace camada {

class SMTSolverImpl : public SMTSolver {
public:
  SMTSolverImpl() = default;
  virtual ~SMTSolverImpl() override = default;

  static SMTExprRef tagExprKind(const SMTExprRef &Exp, SMTExprKind Kind) {
    const_cast<SMTExpr &>(*Exp).setKind(Kind);
    return Exp;
  }

  SMTExprRef newExprRef(const SMTExpr &Exp) const final {
    SMTExprRef theExp = newExprRefImpl(Exp);
#ifndef NDEBUG
    assert(theExp->Sort->isWidthValidated());
#endif
    return theExp;
  }

  SMTSortRef mkBoolSort() override final {
    if (CachedBoolSort)
      return CachedBoolSort;

    SMTSortRef theSort = mkBoolSortImpl();
    assert(theSort->isBoolSort());
    CachedBoolSort = theSort;
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

  SMTSortRef mkRMSort() override final {
    SMTSortRef &CachedSort =
        useCamadaFP ? CachedEncodedRMSort : CachedNativeRMSort;
    if (CachedSort)
      return CachedSort;

    SMTSortRef theSort =
        useCamadaFP ? SMTSolverImpl::mkRMSortImpl() : mkRMSortImpl();
    assert(theSort->isRMSort());
    CachedSort = theSort;
    return theSort;
  }

  SMTSortRef mkFPSort(const unsigned ExpWidth,
                      const unsigned SigWidth) override final {
    assert(ExpWidth && SigWidth);
    auto &Cache = useCamadaFP ? EncodedFPSortCache : NativeFPSortCache;
    FPSortCacheKey Key{ExpWidth, SigWidth};
    auto It = Cache.find(Key);
    if (It != Cache.end())
      return It->second;

    SMTSortRef theSort = useCamadaFP
                             ? SMTSolverImpl::mkFPSortImpl(ExpWidth, SigWidth)
                             : mkFPSortImpl(ExpWidth, SigWidth);
    assert(theSort->isFPSort());
    assert(theSort->getWidth() == (1 + ExpWidth + SigWidth));
    assert(theSort->getWidth() == theSort->getWidthFromSolver());
    Cache.emplace(Key, theSort);
    return theSort;
  }

  SMTSortRef mkFP32Sort() override final { return mkFPSort(8, 23); }

  SMTSortRef mkFP64Sort() override final { return mkFPSort(11, 52); }

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
    SMTExprRef theExp =
        useCamadaFP ? SMTSolverImpl::mkFPAbsImpl(Exp) : mkFPAbsImpl(Exp);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::FPAbs);
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp =
        useCamadaFP ? SMTSolverImpl::mkFPNegImpl(Exp) : mkFPNegImpl(Exp);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::FPNeg);
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPIsInfiniteImpl(Exp)
                                    : mkFPIsInfiniteImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsInfinite);
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp =
        useCamadaFP ? SMTSolverImpl::mkFPIsNaNImpl(Exp) : mkFPIsNaNImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsNaN);
  }

  SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPIsDenormalImpl(Exp)
                                    : mkFPIsDenormalImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsDenormal);
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPIsNormalImpl(Exp)
                                    : mkFPIsNormalImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsNormal);
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp =
        useCamadaFP ? SMTSolverImpl::mkFPIsZeroImpl(Exp) : mkFPIsZeroImpl(Exp);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPIsZero);
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPMulImpl(LHS, RHS, R)
                                    : mkFPMulImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPMul);
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPDivImpl(LHS, RHS, R)
                                    : mkFPDivImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPDiv);
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPRemImpl(LHS, RHS)
                                    : mkFPRemImpl(LHS, RHS);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPRem);
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPAddImpl(LHS, RHS, R)
                                    : mkFPAddImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPAdd);
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPSubImpl(LHS, RHS, R)
                                    : mkFPSubImpl(LHS, RHS, R);
    assert(theExp->Sort == LHS->Sort);
    return tagExprKind(theExp, SMTExprKind::FPSub);
  }

  SMTExprRef mkFPSqrt(const SMTExprRef &Exp,
                      const SMTExprRef &R) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPSqrtImpl(Exp, R)
                                    : mkFPSqrtImpl(Exp, R);
    assert(theExp->Sort == Exp->Sort);
    return tagExprKind(theExp, SMTExprKind::FPSqrt);
  }

  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const SMTExprRef &R) override final {
    assert(X->isFPSort());
    assert(X->Sort == Y->Sort);
    assert(Y->Sort == Z->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPFMAImpl(X, Y, Z, R)
                                    : mkFPFMAImpl(X, Y, Z, R);
    assert(theExp->Sort == Z->Sort);
    return tagExprKind(theExp, SMTExprKind::FPFMA);
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPLtImpl(LHS, RHS)
                                    : mkFPLtImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPLt);
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPGtImpl(LHS, RHS)
                                    : mkFPGtImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPGt);
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPLeImpl(LHS, RHS)
                                    : mkFPLeImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPLe);
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPGeImpl(LHS, RHS)
                                    : mkFPGeImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPGe);
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPEqualImpl(LHS, RHS)
                                    : mkFPEqualImpl(LHS, RHS);
    assert(theExp->isBoolSort());
    return tagExprKind(theExp, SMTExprKind::FPEqual);
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const SMTExprRef &R) override final {
    assert(From->isFPSort());
    assert(To->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPtoFPImpl(From, To, R)
                                    : mkFPtoFPImpl(From, To, R);
    assert(theExp->Sort == To);
    return tagExprKind(theExp, SMTExprKind::FPtoFP);
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const SMTExprRef &R) override final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkSBVtoFPImpl(From, To, R)
                                    : mkSBVtoFPImpl(From, To, R);
    assert(theExp->Sort == To);
    return tagExprKind(theExp, SMTExprKind::SBVtoFP);
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const SMTExprRef &R) override final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkUBVtoFPImpl(From, To, R)
                                    : mkUBVtoFPImpl(From, To, R);
    assert(theExp->Sort == To);
    return tagExprKind(theExp, SMTExprKind::UBVtoFP);
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From,
                       unsigned ToWidth) override final {
    assert(From->isFPSort());
    SMTExprRef theExp = useCamadaFP
                            ? SMTSolverImpl::mkFPtoSBVImpl(From, ToWidth)
                            : mkFPtoSBVImpl(From, ToWidth);
    assert(theExp->getWidth() == ToWidth);
    return tagExprKind(theExp, SMTExprKind::FPtoSBV);
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From,
                       unsigned ToWidth) override final {
    assert(From->isFPSort());
    SMTExprRef theExp = useCamadaFP
                            ? SMTSolverImpl::mkFPtoUBVImpl(From, ToWidth)
                            : mkFPtoUBVImpl(From, ToWidth);
    assert(theExp->getWidth() == ToWidth);
    return tagExprKind(theExp, SMTExprKind::FPtoUBV);
  }

  SMTExprRef mkFPtoIntegral(const SMTExprRef &From,
                            const SMTExprRef &R) override final {
    assert(From->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPtoIntegralImpl(From, R)
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

  std::string getFPInBin(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    return addLeadingZeroes(useCamadaFP ? SMTSolverImpl::getFPInBinImpl(Exp)
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
    SMTExprRef &CachedExpr = b ? CachedTrueExpr : CachedFalseExpr;
    if (CachedExpr)
      return CachedExpr;

    SMTExprRef theExp = mkBoolImpl(b);
    assert(theExp->isBoolSort());
    CachedExpr = theExp;
    return tagExprKind(CachedExpr, SMTExprKind::BoolConst);
  }

  SMTExprRef mkBVFromDec(const int64_t Int,
                         const SMTSortRef &Sort) override final {
    assert(Sort->isBVSort());
    BVDecExprCacheKey Key{Sort.get(), Int};
    auto Cached = BVDecExprCache.find(Key);
    if (Cached != BVDecExprCache.end())
      return Cached->second;

    SMTExprRef theExp = mkBVFromDecImpl(Int, Sort);
    assert(theExp->isBVSort());
    assert(theExp->getWidth() == Sort->getWidth());
    BVDecExprCache.emplace(Key, theExp);
    return tagExprKind(theExp, SMTExprKind::BVConst);
  }

  SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) override final {
    return mkBVFromDec(Int, mkBVSort(BitWidth));
  }

  SMTExprRef mkBVFromBin(const std::string &Int,
                         const SMTSortRef &Sort) override final {
    assert(Sort->isBVSort());
    BVBinExprCacheKey Key{Sort.get(), Int};
    auto Cached = BVBinExprCache.find(Key);
    if (Cached != BVBinExprCache.end())
      return Cached->second;

    SMTExprRef theExp = mkBVFromBinImpl(Int, Sort);
    assert(theExp->isBVSort());
    assert(theExp->getWidth() == Sort->getWidth());
    BVBinExprCache.emplace(Key, theExp);
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

  SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth) override {
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkFPFromBinImpl(FP, EWidth)
                                    : mkFPFromBinImpl(FP, EWidth);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == FP.length());
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkFP32(const float Float) override final {
    SMTExprRef theExp = mkFP32Impl(Float);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == 32);
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkFP64(const double Double) override final {
    SMTExprRef theExp = mkFP64Impl(Double);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == 64);
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkRM(const RM &R) override final {
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkRMImpl(R) : mkRMImpl(R);
    assert(theExp->isRMSort());
    return tagExprKind(theExp, SMTExprKind::RMConst);
  }

  SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) override final {
    SMTExprRef theExp = useCamadaFP
                            ? SMTSolverImpl::mkNaNImpl(Sgn, ExpWidth, SigWidth)
                            : mkNaNImpl(Sgn, ExpWidth, SigWidth);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == (ExpWidth + SigWidth));
    assert(theExp->getWidth() == theExp->Sort->getWidthFromSolver());
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkNaN32(const bool Sgn) override final {
    return mkNaN(Sgn, 8, 24);
  }

  SMTExprRef mkNaN64(const bool Sgn) override final {
    return mkNaN(Sgn, 11, 53);
  }

  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) override final {
    SMTExprRef theExp = useCamadaFP
                            ? SMTSolverImpl::mkInfImpl(Sgn, ExpWidth, SigWidth)
                            : mkInfImpl(Sgn, ExpWidth, SigWidth);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == (ExpWidth + SigWidth));
    assert(theExp->getWidth() == theExp->Sort->getWidthFromSolver());
    return tagExprKind(theExp, SMTExprKind::FPConst);
  }

  SMTExprRef mkInf32(const bool Sgn) override final {
    return mkInf(Sgn, 8, 24);
  }

  SMTExprRef mkInf64(const bool Sgn) override final {
    return mkInf(Sgn, 11, 53);
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
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkBVToIEEEFPImpl(Exp, To)
                                    : mkBVToIEEEFPImpl(Exp, To);
    assert(theExp->isFPSort());
    assert(theExp->getWidth() == Exp->getWidth());
    return tagExprKind(theExp, SMTExprKind::BVToIEEEFP);
  }

  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) override final {
    assert(Exp->isFPSort());
    SMTExprRef theExp = useCamadaFP ? SMTSolverImpl::mkIEEEFPToBVImpl(Exp)
                                    : mkIEEEFPToBVImpl(Exp);
    assert(theExp->isBVSort());
    assert(theExp->getWidth() == Exp->getWidth());
    return tagExprKind(theExp, SMTExprKind::IEEEFPToBV);
  }

  checkResult check() override final { return checkImpl(); }

  void reset() override final {
    invalidateGeneratedObjects();
    return resetImpl();
  }

  void dump() override final { return dumpImpl(); }

  void dumpModel() override final { return dumpModelImpl(); }

  SMTSortRef mkBVFPSort(const unsigned ExpWidth,
                        const unsigned SigWidth) override final {
    FPSortCacheKey Key{ExpWidth, SigWidth};
    auto It = EncodedFPSortCache.find(Key);
    if (It != EncodedFPSortCache.end())
      return It->second;

    SMTSortRef theSort = mkBVFPSortImpl(ExpWidth, SigWidth);
    assert(theSort->isFPSort());
    assert(theSort->getWidth() == (1 + ExpWidth + SigWidth));
    assert(theSort->getWidth() == theSort->getWidthFromSolver());
    EncodedFPSortCache.emplace(Key, theSort);
    return theSort;
  }

  SMTSortRef mkBVRMSort() override final {
    if (CachedEncodedRMSort)
      return CachedEncodedRMSort;

    SMTSortRef theSort = mkBVRMSortImpl();
    assert(theSort->isRMSort());
    CachedEncodedRMSort = theSort;
    return theSort;
  }

protected:
  virtual SMTExprRef newExprRefImpl(const SMTExpr &Exp) const = 0;

  virtual SMTExprRef cloneExprWithSortImpl(const SMTExpr &Exp,
                                           const SMTSortRef &Sort) const = 0;

  virtual SMTSortRef mkBoolSortImpl() = 0;

  virtual SMTSortRef mkBVSortImpl(const unsigned BitWidth) = 0;

  virtual SMTSortRef mkRMSortImpl();

  virtual SMTSortRef mkFPSortImpl(const unsigned ExpWidth,
                                  const unsigned SigWidth);

  virtual SMTSortRef mkArraySortImpl(const SMTSortRef &IndexSort,
                                     const SMTSortRef &ElemSort) = 0;

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
    return mkIte(mkNot(comp), mkBVFromDec(1, 1), mkBVFromDec(0, 1));
  }

  virtual SMTExprRef mkBVRedAndImpl(const SMTExprRef &Exp) {
    // bvredand = bvcomp(x,-1) ? bv1 : bv0;
    SMTExprRef comp = mkEqual(Exp, mkBVFromDec(-1, Exp->getWidth()));
    return mkIte(comp, mkBVFromDec(1, 1), mkBVFromDec(0, 1));
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

  virtual bool getBoolImpl(const SMTExprRef &Exp) = 0;

  int64_t getBVImpl(const SMTExprRef &Exp);

  virtual std::string getBVInBinImpl(const SMTExprRef &Exp) = 0;

  virtual std::string getFPInBinImpl(const SMTExprRef &Exp);

  float getFP32Impl(const SMTExprRef &Exp);

  double getFP64Impl(const SMTExprRef &Exp);

  virtual SMTExprRef getArrayElementImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) = 0;

  virtual SMTExprRef mkBoolImpl(const bool b) = 0;

  virtual SMTExprRef mkBVFromDecImpl(const int64_t Int,
                                     const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkBVFromBinImpl(const std::string &Int,
                                     const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkSymbolImpl(const std::string &Name,
                                  const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkFPFromBinImpl(const std::string &FP, unsigned EWidth);

  SMTExprRef mkFP32Impl(const float Float);

  SMTExprRef mkFP64Impl(const double Double);

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

  virtual void dumpImpl();

  virtual void dumpModelImpl();

  virtual SMTSortRef mkBVFPSortImpl(const unsigned ExpWidth,
                                    const unsigned SigWidth) = 0;

  virtual SMTSortRef mkBVRMSortImpl() = 0;
};

} // namespace camada

#endif
