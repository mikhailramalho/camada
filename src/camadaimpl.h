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

namespace camada {

class SMTSolverImpl : public SMTSolver {
public:
  SMTSolverImpl() = default;
  virtual ~SMTSolverImpl() override = default;

  SMTExprRef newExprRef(const SMTExpr &Exp) const final {
    SMTExprRef theExpr = newExprRefImpl(Exp);
    return theExpr;
  }

  SMTSortRef mkBoolSort() final {
    SMTSortRef theSort = mkBoolSortImpl();
    return theSort;
  }

  SMTSortRef mkBVSort(const unsigned BitWidth) final {
    assert(BitWidth);
    SMTSortRef theSort = mkBVSortImpl(BitWidth);
    return theSort;
  }

  SMTSortRef mkRMSort() final {
    SMTSortRef theSort =
        useCamadaFP ? SMTSolverImpl::mkRMSortImpl() : mkRMSortImpl();
    return theSort;
  }

  SMTSortRef mkFPSort(const unsigned ExpWidth, const unsigned SigWidth) final {
    assert(ExpWidth && SigWidth);
    SMTSortRef theSort = useCamadaFP
                             ? SMTSolverImpl::mkFPSortImpl(ExpWidth, SigWidth)
                             : mkFPSortImpl(ExpWidth, SigWidth);
    return theSort;
  }

  SMTSortRef mkFP32Sort() final { return mkFPSort(8, 23); }

  SMTSortRef mkFP64Sort() final { return mkFPSort(11, 52); }

  SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                         const SMTSortRef &ElemSort) final {
    SMTSortRef theSort = mkArraySortImpl(IndexSort, ElemSort);
    return theSort;
  }

  void addConstraint(const SMTExprRef &Exp) final {
    return addConstraintImpl(Exp);
  }

  SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVAddImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVSubImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVMulImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVSRemImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVURemImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVSDivImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVUDivImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVShlImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVAshrImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVLshrImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    SMTExprRef theExpr = mkBVNegImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkBVNot(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    SMTExprRef theExpr = mkBVNotImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVXorImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVOrImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVAndImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVUltImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVSltImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVUgtImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVSgtImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVUleImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVSleImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVUgeImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkBVSgeImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkNot(const SMTExprRef &Exp) final {
    assert(Exp->isBoolSort());
    SMTExprRef theExpr = mkNotImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort() || LHS->isBVSort() || LHS->isArraySort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkEqualImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkAndImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkOrImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = mkXorImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) final {
    assert(Cond->isBoolSort());
    assert(T->isBVSort() || T->isArraySort());
    assert(T->Sort == F->Sort);
    SMTExprRef theExpr = mkIteImpl(Cond, T, F);
    return theExpr;
  }

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    SMTExprRef theExpr = mkBVSignExtImpl(i, Exp);
    return theExpr;
  }

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    SMTExprRef theExpr = mkBVZeroExtImpl(i, Exp);
    return theExpr;
  }

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    assert(High >= Low);
    assert(High <= Exp->getWidth());
    assert(Low <= Exp->getWidth());
    SMTExprRef theExpr = mkBVExtractImpl(High, Low, Exp);
    return theExpr;
  }

  SMTExprRef mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(RHS->isBVSort());
    SMTExprRef theExpr = mkBVConcatImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkBVRedOr(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    SMTExprRef theExpr = mkBVRedOrImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkBVRedAnd(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    SMTExprRef theExpr = mkBVRedAndImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPAbs(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr =
        useCamadaFP ? SMTSolverImpl::mkFPAbsImpl(Exp) : mkFPAbsImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr =
        useCamadaFP ? SMTSolverImpl::mkFPNegImpl(Exp) : mkFPNegImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPIsInfiniteImpl(Exp)
                                     : mkFPIsInfiniteImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr =
        useCamadaFP ? SMTSolverImpl::mkFPIsNaNImpl(Exp) : mkFPIsNaNImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPIsDenormalImpl(Exp)
                                     : mkFPIsDenormalImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPIsNormalImpl(Exp)
                                     : mkFPIsNormalImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr =
        useCamadaFP ? SMTSolverImpl::mkFPIsZeroImpl(Exp) : mkFPIsZeroImpl(Exp);
    return theExpr;
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPMulImpl(LHS, RHS, R)
                                     : mkFPMulImpl(LHS, RHS, R);
    return theExpr;
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPDivImpl(LHS, RHS, R)
                                     : mkFPDivImpl(LHS, RHS, R);
    return theExpr;
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPRemImpl(LHS, RHS)
                                     : mkFPRemImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPAddImpl(LHS, RHS, R)
                                     : mkFPAddImpl(LHS, RHS, R);
    return theExpr;
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPSubImpl(LHS, RHS, R)
                                     : mkFPSubImpl(LHS, RHS, R);
    return theExpr;
  }

  SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RM &R) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPSqrtImpl(Exp, R)
                                     : mkFPSqrtImpl(Exp, R);
    return theExpr;
  }

  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const RM &R) final {
    assert(X->isFPSort());
    assert(X->Sort == Y->Sort);
    assert(Y->Sort == Z->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPFMAImpl(X, Y, Z, R)
                                     : mkFPFMAImpl(X, Y, Z, R);
    return theExpr;
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPLtImpl(LHS, RHS)
                                     : mkFPLtImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPGtImpl(LHS, RHS)
                                     : mkFPGtImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPLeImpl(LHS, RHS)
                                     : mkFPLeImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPGeImpl(LHS, RHS)
                                     : mkFPGeImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPEqualImpl(LHS, RHS)
                                     : mkFPEqualImpl(LHS, RHS);
    return theExpr;
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const RM &R) final {
    assert(From->isFPSort());
    assert(To->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkFPtoFPImpl(From, To, R)
                                     : mkFPtoFPImpl(From, To, R);
    return theExpr;
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkSBVtoFPImpl(From, To, R)
                                     : mkSBVtoFPImpl(From, To, R);
    return theExpr;
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkUBVtoFPImpl(From, To, R)
                                     : mkUBVtoFPImpl(From, To, R);
    return theExpr;
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) final {
    assert(From->isFPSort());
    SMTExprRef theExpr = useCamadaFP
                             ? SMTSolverImpl::mkFPtoSBVImpl(From, ToWidth)
                             : mkFPtoSBVImpl(From, ToWidth);
    return theExpr;
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) final {
    assert(From->isFPSort());
    SMTExprRef theExpr = useCamadaFP
                             ? SMTSolverImpl::mkFPtoUBVImpl(From, ToWidth)
                             : mkFPtoUBVImpl(From, ToWidth);
    return theExpr;
  }

  SMTExprRef mkFPtoIntegral(const SMTExprRef &From, const RM &R) final {
    assert(From->isFPSort());
    SMTExprRef theExpr = useCamadaFP
                             ? SMTSolverImpl::mkFPtoIntegralImpl(From, R)
                             : mkFPtoIntegralImpl(From, R);
    return theExpr;
  }

  SMTExprRef mkArraySelect(const SMTExprRef &Array,
                           const SMTExprRef &Index) final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    SMTExprRef theExpr = mkArraySelectImpl(Array, Index);
    return theExpr;
  }

  SMTExprRef mkArrayStore(const SMTExprRef &Array, const SMTExprRef &Index,
                          const SMTExprRef &Element) final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    assert(Array->Sort->getElementSort() == Element->Sort);
    SMTExprRef theExpr = mkArrayStoreImpl(Array, Index, Element);
    return theExpr;
  }

  bool getBool(const SMTExprRef &Exp) final {
    assert(Exp->isBoolSort());
    bool theBool = getBoolImpl(Exp);
    return theBool;
  }

  int64_t getBV(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    int64_t theInt = getBVImpl(Exp);
    return theInt;
  }

  std::string getBVInBin(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    std::string theBV = getBVInBinImpl(Exp);
    return theBV;
  }

  std::string getFPInBin(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    std::string theFP =
        useCamadaFP ? SMTSolverImpl::getFPInBinImpl(Exp) : getFPInBinImpl(Exp);
    return theFP;
  }

  float getFP32(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    float theFP = getFP32Impl(Exp);
    return theFP;
  }

  double getFP64(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    double theFP = getFP64Impl(Exp);
    return theFP;
  }

  SMTExprRef getArrayElement(const SMTExprRef &Array,
                             const SMTExprRef &Index) final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    SMTExprRef theExpr = getArrayElementImpl(Array, Index);
    return theExpr;
  }

  SMTExprRef mkBool(const bool b) final {
    SMTExprRef theExpr = mkBoolImpl(b);
    return theExpr;
  }

  SMTExprRef mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) final {
    SMTExprRef theExpr = mkBVFromDecImpl(Int, Sort);
    return theExpr;
  }

  SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) final {
    SMTExprRef theExpr = mkBVFromDecImpl(Int, mkBVSort(BitWidth));
    return theExpr;
  }

  SMTExprRef mkBVFromBin(const std::string &Int, const SMTSortRef &Sort) final {
    assert(Sort->isBVSort());
    SMTExprRef theExpr = mkBVFromBinImpl(Int, Sort);
    return theExpr;
  }

  SMTExprRef mkBVFromBin(const std::string &Int, unsigned BitWidth) final {
    SMTExprRef theExpr = mkBVFromBin(Int, mkBVSort(BitWidth));
    return theExpr;
  }

  SMTExprRef mkBVFromBin(const std::string &Int) final {
    SMTExprRef theExpr = mkBVFromBin(Int, Int.length());
    return theExpr;
  }

  SMTExprRef mkSymbol(const std::string &Name, SMTSortRef Sort) final {
    SMTExprRef theExpr = mkSymbolImpl(Name, Sort);
    return theExpr;
  }

  SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth) override {
    SMTExprRef theExpr = useCamadaFP
                             ? SMTSolverImpl::mkFPFromBinImpl(FP, EWidth)
                             : mkFPFromBinImpl(FP, EWidth);
    return theExpr;
  }

  SMTExprRef mkFP32(const float Float) final {
    SMTExprRef theExpr = mkFP32Impl(Float);
    return theExpr;
  }

  SMTExprRef mkFP64(const double Double) final {
    SMTExprRef theExpr = mkFP64Impl(Double);
    return theExpr;
  }

  SMTExprRef mkRM(const RM &R) final {
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkRMImpl(R) : mkRMImpl(R);
    return theExpr;
  }

  SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) final {
    SMTExprRef theExpr = useCamadaFP
                             ? SMTSolverImpl::mkNaNImpl(Sgn, ExpWidth, SigWidth)
                             : mkNaNImpl(Sgn, ExpWidth, SigWidth);
    return theExpr;
  }

  SMTExprRef mkNaN32(const bool Sgn) final { return mkNaN(Sgn, 8, 23); }

  SMTExprRef mkNaN64(const bool Sgn) final { return mkNaN(Sgn, 11, 52); }

  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) final {
    SMTExprRef theExpr = useCamadaFP
                             ? SMTSolverImpl::mkInfImpl(Sgn, ExpWidth, SigWidth)
                             : mkInfImpl(Sgn, ExpWidth, SigWidth);
    return theExpr;
  }

  SMTExprRef mkInf32(const bool Sgn) final { return mkInf(Sgn, 8, 23); }

  SMTExprRef mkInf64(const bool Sgn) final { return mkInf(Sgn, 11, 52); }

  SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                          const SMTExprRef &InitValue) final {
    SMTExprRef theExpr = mkArrayConstImpl(IndexSort, InitValue);
    return theExpr;
  }

  SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp, const SMTSortRef &To) final {
    assert(Exp->isBVSort() && To->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkBVToIEEEFPImpl(Exp, To)
                                     : mkBVToIEEEFPImpl(Exp, To);
    return theExpr;
  }

  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    SMTExprRef theExpr = useCamadaFP ? SMTSolverImpl::mkIEEEFPToBVImpl(Exp)
                                     : mkIEEEFPToBVImpl(Exp);
    return theExpr;
  }

  checkResult check() final { return checkImpl(); }

  void reset() final { return resetImpl(); }

  void dump() final { return dumpImpl(); }

  void dumpModel() final { return dumpModelImpl(); }

  SMTSortRef mkBVFPSort(const unsigned ExpWidth,
                        const unsigned SigWidth) final {
    SMTSortRef theSort = mkBVFPSortImpl(ExpWidth, SigWidth);
    return theSort;
  }

  SMTSortRef mkBVRMSort() final {
    SMTSortRef theSort = mkBVRMSortImpl();
    return theSort;
  }

protected:
  virtual SMTExprRef newExprRefImpl(const SMTExpr &Exp) const = 0;

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
                                 const RM &R);

  virtual SMTExprRef mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const RM &R);

  virtual SMTExprRef mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const RM &R);

  virtual SMTExprRef mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const RM &R);

  virtual SMTExprRef mkFPSqrtImpl(const SMTExprRef &Exp, const RM &R);

  virtual SMTExprRef mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                 const SMTExprRef &Z, const RM &R);

  virtual SMTExprRef mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPGtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkFPLt(RHS, LHS);
  }

  virtual SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPGeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkFPLt(RHS, LHS));
  }

  virtual SMTExprRef mkFPEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                  const RM &R);

  virtual SMTExprRef mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const RM &R);

  virtual SMTExprRef mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const RM &R);

  virtual SMTExprRef mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoIntegralImpl(const SMTExprRef &From, const RM &R);

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

  virtual SMTExprRef mkSymbolImpl(const std::string &Name, SMTSortRef Sort) = 0;

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
