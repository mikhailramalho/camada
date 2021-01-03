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

namespace camada {

class SMTSolverImpl : public SMTSolver {
public:
  SMTSolverImpl() = default;
  virtual ~SMTSolverImpl() override = default;

  SMTSortRef mkRMSort() final {
    if (useCamadaFP)
      return SMTSolverImpl::mkRMSortImpl();
    return mkRMSortImpl();
  }

  SMTSortRef mkFPSort(const unsigned ExpWidth, const unsigned SigWidth) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPSortImpl(ExpWidth, SigWidth);
    return mkFPSortImpl(ExpWidth, SigWidth);
  }

  SMTExprRef mkFPAbs(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPAbsImpl(Exp);
    return mkFPAbsImpl(Exp);
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPNegImpl(Exp);
    return mkFPNegImpl(Exp);
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsInfiniteImpl(Exp);
    return mkFPIsInfiniteImpl(Exp);
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsNaNImpl(Exp);
    return mkFPIsNaNImpl(Exp);
  }

  SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsDenormalImpl(Exp);
    return mkFPIsDenormalImpl(Exp);
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsNormalImpl(Exp);
    return mkFPIsNormalImpl(Exp);
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPIsZeroImpl(Exp);
    return mkFPIsZeroImpl(Exp);
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPMulImpl(LHS, RHS, R);
    return mkFPMulImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPDivImpl(LHS, RHS, R);
    return mkFPDivImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPRemImpl(LHS, RHS);
    return mkFPRemImpl(LHS, RHS);
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPAddImpl(LHS, RHS, R);
    return mkFPAddImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPSubImpl(LHS, RHS, R);
    return mkFPSubImpl(LHS, RHS, R);
  }

  SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPSqrtImpl(Exp, R);
    return mkFPSqrtImpl(Exp, R);
  }

  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPFMAImpl(X, Y, Z, R);
    return mkFPFMAImpl(X, Y, Z, R);
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPLtImpl(LHS, RHS);
    return mkFPLtImpl(LHS, RHS);
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPLeImpl(LHS, RHS);
    return mkFPLeImpl(LHS, RHS);
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPEqualImpl(LHS, RHS);
    return mkFPEqualImpl(LHS, RHS);
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoFPImpl(From, To, R);
    return mkFPtoFPImpl(From, To, R);
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkSBVtoFPImpl(From, To, R);
    return mkSBVtoFPImpl(From, To, R);
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkUBVtoFPImpl(From, To, R);
    return mkUBVtoFPImpl(From, To, R);
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoSBVImpl(From, ToWidth);
    return mkFPtoSBVImpl(From, ToWidth);
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoUBVImpl(From, ToWidth);
    return mkFPtoUBVImpl(From, ToWidth);
  }

  SMTExprRef mkFPtoIntegral(const SMTExprRef &From, const RM &R) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPtoIntegralImpl(From, R);
    return mkFPtoIntegralImpl(From, R);
  }

  std::string getFPInBin(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::getFPInBinImpl(Exp);
    return getFPInBinImpl(Exp);
  }

  SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth) override {
    if (useCamadaFP)
      return SMTSolverImpl::mkFPFromBinImpl(FP, EWidth);
    return mkFPFromBinImpl(FP, EWidth);
  }

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

  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkInfImpl(Sgn, ExpWidth, SigWidth);
    return mkInfImpl(Sgn, ExpWidth, SigWidth);
  }

  SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp, const SMTSortRef &To) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkBVToIEEEFPImpl(Exp, To);
    return mkBVToIEEEFPImpl(Exp, To);
  }

  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) final {
    if (useCamadaFP)
      return SMTSolverImpl::mkIEEEFPToBVImpl(Exp);
    return mkIEEEFPToBVImpl(Exp);
  }

protected:
  virtual SMTSortRef mkRMSortImpl();

  virtual SMTSortRef mkFPSortImpl(const unsigned ExpWidth,
                                  const unsigned SigWidth);

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

  virtual SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

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

  virtual std::string getFPInBinImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPFromBinImpl(const std::string &FP, unsigned EWidth);

  virtual SMTExprRef mkRMImpl(const RM &R);

  virtual SMTExprRef mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                      const SMTSortRef &To);

  virtual SMTExprRef mkIEEEFPToBVImpl(const SMTExprRef &Exp);

  SMTExprRef mkToBV(const SMTExprRef &Exp, bool isSigned, unsigned int width);

  SMTExprRef round(const SMTExprRef &R, const SMTExprRef &Sgn, SMTExprRef &Sig,
                   SMTExprRef &Exp, unsigned EWidth, unsigned SWidth);
};

} // namespace camada

#endif
