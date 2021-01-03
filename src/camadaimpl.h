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
    return newExprRefImpl(Exp);
  }

  SMTSortRef mkBoolSort() final { return mkBoolSortImpl(); }

  SMTSortRef mkBVSort(const unsigned BitWidth) final {
    assert(BitWidth);
    return mkBVSortImpl(BitWidth);
  }

  SMTSortRef mkRMSort() final {
    if (useCamadaFP)
      return SMTSolverImpl::mkRMSortImpl();
    return mkRMSortImpl();
  }

  SMTSortRef mkFPSort(const unsigned ExpWidth, const unsigned SigWidth) final {
    assert(ExpWidth && SigWidth);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPSortImpl(ExpWidth, SigWidth);
    return mkFPSortImpl(ExpWidth, SigWidth);
  }

  SMTSortRef mkFP32Sort() final { return mkFPSort(8, 23); }

  SMTSortRef mkFP64Sort() final { return mkFPSort(11, 52); }

  SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                         const SMTSortRef &ElemSort) final {
    return mkArraySortImpl(IndexSort, ElemSort);
  }

  void addConstraint(const SMTExprRef &Exp) final {
    return addConstraintImpl(Exp);
  }

  SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVAddImpl(LHS, RHS);
  }

  SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVSubImpl(LHS, RHS);
  }

  SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVMulImpl(LHS, RHS);
  }

  SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVSRemImpl(LHS, RHS);
  }

  SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVURemImpl(LHS, RHS);
  }

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVSDivImpl(LHS, RHS);
  }

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVUDivImpl(LHS, RHS);
  }

  SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVShlImpl(LHS, RHS);
  }

  SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVAshrImpl(LHS, RHS);
  }

  SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVLshrImpl(LHS, RHS);
  }

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return mkBVNegImpl(Exp);
  }

  SMTExprRef mkBVNot(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return mkBVNotImpl(Exp);
  }

  SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVXorImpl(LHS, RHS);
  }

  SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVOrImpl(LHS, RHS);
  }

  SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVAndImpl(LHS, RHS);
  }

  SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVUltImpl(LHS, RHS);
  }

  SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVSltImpl(LHS, RHS);
  }

  SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVUgtImpl(LHS, RHS);
  }

  SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVSgtImpl(LHS, RHS);
  }

  SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVUleImpl(LHS, RHS);
  }

  SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVSleImpl(LHS, RHS);
  }

  SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVUgeImpl(LHS, RHS);
  }

  SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(LHS->Sort == RHS->Sort);
    return mkBVSgeImpl(LHS, RHS);
  }

  SMTExprRef mkNot(const SMTExprRef &Exp) final {
    assert(Exp->isBoolSort());
    return mkNotImpl(Exp);
  }

  SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort() || LHS->isBVSort() || LHS->isArraySort());
    assert(LHS->Sort == RHS->Sort);
    return mkEqualImpl(LHS, RHS);
  }

  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    return mkAndImpl(LHS, RHS);
  }

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    return mkOrImpl(LHS, RHS);
  }

  SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBoolSort());
    assert(LHS->Sort == RHS->Sort);
    return mkXorImpl(LHS, RHS);
  }

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) final {
    assert(Cond->isBoolSort());
    assert(T->isBVSort() || T->isArraySort());
    assert(T->Sort == F->Sort);
    return mkIteImpl(Cond, T, F);
  }

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return mkBVSignExtImpl(i, Exp);
  }

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return mkBVZeroExtImpl(i, Exp);
  }

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    assert(High >= Low);
    assert(High <= Exp->getWidth());
    assert(Low <= Exp->getWidth());
    return mkBVExtractImpl(High, Low, Exp);
  }

  SMTExprRef mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isBVSort());
    assert(RHS->isBVSort());
    return mkBVConcatImpl(LHS, RHS);
  }

  SMTExprRef mkBVRedOr(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return mkBVRedOrImpl(Exp);
  }

  SMTExprRef mkBVRedAnd(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return mkBVRedAndImpl(Exp);
  }

  SMTExprRef mkFPAbs(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPAbsImpl(Exp);
    return mkFPAbsImpl(Exp);
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPNegImpl(Exp);
    return mkFPNegImpl(Exp);
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsInfiniteImpl(Exp);
    return mkFPIsInfiniteImpl(Exp);
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsNaNImpl(Exp);
    return mkFPIsNaNImpl(Exp);
  }

  SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsDenormalImpl(Exp);
    return mkFPIsDenormalImpl(Exp);
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsNormalImpl(Exp);
    return mkFPIsNormalImpl(Exp);
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsZeroImpl(Exp);
    return mkFPIsZeroImpl(Exp);
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPMulImpl(LHS, RHS, R);
    return mkFPMulImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPDivImpl(LHS, RHS, R);
    return mkFPDivImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPRemImpl(LHS, RHS);
    return mkFPRemImpl(LHS, RHS);
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPAddImpl(LHS, RHS, R);
    return mkFPAddImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPSubImpl(LHS, RHS, R);
    return mkFPSubImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RM &R) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPSqrtImpl(Exp, R);
    return mkFPSqrtImpl(Exp, R);
  }

  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const RM &R) final {
    assert(X->isFPSort());
    assert(X->Sort == Y->Sort);
    assert(Y->Sort == Z->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPFMAImpl(X, Y, Z, R);
    return mkFPFMAImpl(X, Y, Z, R);
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPLtImpl(LHS, RHS);
    return mkFPLtImpl(LHS, RHS);
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPGtImpl(LHS, RHS);
    return mkFPGtImpl(LHS, RHS);
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPLeImpl(LHS, RHS);
    return mkFPLeImpl(LHS, RHS);
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPGeImpl(LHS, RHS);
    return mkFPGeImpl(LHS, RHS);
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    assert(LHS->isFPSort());
    assert(LHS->Sort == RHS->Sort);
    if (useCamadaFP)
      return SMTSolverImpl::mkFPEqualImpl(LHS, RHS);
    return mkFPEqualImpl(LHS, RHS);
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const RM &R) final {
    assert(From->isFPSort());
    assert(To->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoFPImpl(From, To, R);
    return mkFPtoFPImpl(From, To, R);
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkSBVtoFPImpl(From, To, R);
    return mkSBVtoFPImpl(From, To, R);
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) final {
    assert(From->isBVSort());
    assert(To->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkUBVtoFPImpl(From, To, R);
    return mkUBVtoFPImpl(From, To, R);
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) final {
    assert(From->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoSBVImpl(From, ToWidth);
    return mkFPtoSBVImpl(From, ToWidth);
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) final {
    assert(From->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoUBVImpl(From, ToWidth);
    return mkFPtoUBVImpl(From, ToWidth);
  }

  SMTExprRef mkFPtoIntegral(const SMTExprRef &From, const RM &R) final {
    assert(From->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoIntegralImpl(From, R);
    return mkFPtoIntegralImpl(From, R);
  }

  SMTExprRef mkArraySelect(const SMTExprRef &Array,
                           const SMTExprRef &Index) final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    return mkArraySelectImpl(Array, Index);
  }

  SMTExprRef mkArrayStore(const SMTExprRef &Array, const SMTExprRef &Index,
                          const SMTExprRef &Element) final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    assert(Array->Sort->getElementSort() == Element->Sort);
    return mkArrayStoreImpl(Array, Index, Element);
  }

  bool getBool(const SMTExprRef &Exp) final {
    assert(Exp->isBoolSort());
    return getBoolImpl(Exp);
  }

  int64_t getBV(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return getBVImpl(Exp);
  }

  std::string getBVInBin(const SMTExprRef &Exp) final {
    assert(Exp->isBVSort());
    return getBVInBinImpl(Exp);
  }

  std::string getFPInBin(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::getFPInBinImpl(Exp);
    return getFPInBinImpl(Exp);
  }

  float getFP32(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    return getFP32Impl(Exp);
  }

  double getFP64(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    return getFP64Impl(Exp);
  }

  SMTExprRef getArrayElement(const SMTExprRef &Array,
                             const SMTExprRef &Index) final {
    assert(Array->isArraySort());
    assert(Array->Sort->getIndexSort() == Index->Sort);
    return getArrayElementImpl(Array, Index);
  }

  SMTExprRef mkBool(const bool b) final { return mkBoolImpl(b); }

  SMTExprRef mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) final {
    return mkBVFromDecImpl(Int, Sort);
  }

  SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) final {
    return mkBVFromDecImpl(Int, mkBVSort(BitWidth));
  }

  SMTExprRef mkBVFromBin(const std::string &Int, const SMTSortRef &Sort) final {
    assert(Sort->isBVSort());
    return mkBVFromBinImpl(Int, Sort);
  }

  SMTExprRef mkBVFromBin(const std::string &Int, unsigned BitWidth) final {
    return mkBVFromBin(Int, mkBVSort(BitWidth));
  }

  SMTExprRef mkBVFromBin(const std::string &Int) final {
    return mkBVFromBin(Int, Int.length());
  }

  SMTExprRef mkSymbol(const std::string &Name, SMTSortRef Sort) final {
    return mkSymbolImpl(Name, Sort);
  }

  SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth) override {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPFromBinImpl(FP, EWidth);
    return mkFPFromBinImpl(FP, EWidth);
  }

  SMTExprRef mkFP32(const float Float) final { return mkFP32Impl(Float); }

  SMTExprRef mkFP64(const double Double) final { return mkFP64Impl(Double); }

  SMTExprRef mkRM(const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkRMImpl(R);
    return mkRMImpl(R);
  }

  SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkNaNImpl(Sgn, ExpWidth, SigWidth);
    return mkNaNImpl(Sgn, ExpWidth, SigWidth);
  }

  SMTExprRef mkNaN32(const bool Sgn) final { return mkNaN(Sgn, 8, 23); }

  SMTExprRef mkNaN64(const bool Sgn) final { return mkNaN(Sgn, 11, 52); }

  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkInfImpl(Sgn, ExpWidth, SigWidth);
    return mkInfImpl(Sgn, ExpWidth, SigWidth);
  }

  SMTExprRef mkInf32(const bool Sgn) final { return mkInf(Sgn, 8, 23); }

  SMTExprRef mkInf64(const bool Sgn) final { return mkInf(Sgn, 11, 52); }

  SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                          const SMTExprRef &InitValue) final {
    return mkArrayConstImpl(IndexSort, InitValue);
  }

  SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp, const SMTSortRef &To) final {
    assert(Exp->isBVSort() && To->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkBVToIEEEFPImpl(Exp, To);
    return mkBVToIEEEFPImpl(Exp, To);
  }

  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) final {
    assert(Exp->isFPSort());
    if (useCamadaFP)
      return SMTSolverImpl::mkIEEEFPToBVImpl(Exp);
    return mkIEEEFPToBVImpl(Exp);
  }

  checkResult check() final { return checkImpl(); }

  void reset() final { return resetImpl(); }

  void dump() final { return dumpImpl(); }

  void dumpModel() final { return dumpModelImpl(); }

  SMTSortRef mkBVFPSort(const unsigned ExpWidth,
                        const unsigned SigWidth) final {
    return mkBVFPSortImpl(ExpWidth, SigWidth);
  }

  SMTSortRef mkBVRMSort() final { return mkBVRMSortImpl(); }

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
