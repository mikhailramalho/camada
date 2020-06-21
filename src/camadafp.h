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

#ifndef CAMADAFP_H_
#define CAMADAFP_H_

#include "camada.h"

namespace camada {

class SMTFPSolver : public SMTSolver {
public:
  SMTFPSolver() = default;
  ~SMTFPSolver() = default;

  virtual SMTSortRef getRoundingModeSort() override {
    if (useCamadaFP)
      return SMTFPSolver::getRoundingModeSortImpl();
    return getRoundingModeSortImpl();
  }

  virtual SMTSortRef getFloatSort(const unsigned ExpWidth,
                                  const unsigned SigWidth) override {
    if (useCamadaFP)
      return SMTFPSolver::getFloatSortImpl(ExpWidth, SigWidth);
    return getFloatSortImpl(ExpWidth, SigWidth);
  }

  virtual SMTExprRef mkFPAbs(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPAbsImpl(Exp);
    return mkFPAbsImpl(Exp);
  }

  virtual SMTExprRef mkFPNeg(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPNegImpl(Exp);
    return mkFPNegImpl(Exp);
  }

  virtual SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPIsInfiniteImpl(Exp);
    return mkFPIsInfiniteImpl(Exp);
  }

  virtual SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPIsNaNImpl(Exp);
    return mkFPIsNaNImpl(Exp);
  }

  virtual SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPIsDenormalImpl(Exp);
    return mkFPIsDenormalImpl(Exp);
  }

  virtual SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPIsNormalImpl(Exp);
    return mkFPIsNormalImpl(Exp);
  }

  virtual SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPIsZeroImpl(Exp);
    return mkFPIsZeroImpl(Exp);
  }

  virtual SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPMulImpl(LHS, RHS, R);
    return mkFPMulImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPDivImpl(LHS, RHS, R);
    return mkFPDivImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPRem(const SMTExprRef &LHS,
                             const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPRemImpl(LHS, RHS);
    return mkFPRemImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPAddImpl(LHS, RHS, R);
    return mkFPAddImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPSubImpl(LHS, RHS, R);
    return mkFPSubImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPSqrt(const SMTExprRef &Exp,
                              const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPSqrtImpl(Exp, R);
    return mkFPSqrtImpl(Exp, R);
  }

  virtual SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPFMAImpl(X, Y, Z, R);
    return mkFPFMAImpl(X, Y, Z, R);
  };

  virtual SMTExprRef mkFPLt(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPLtImpl(LHS, RHS);
    return mkFPLtImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPLe(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPLeImpl(LHS, RHS);
    return mkFPLeImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPEqualImpl(LHS, RHS);
    return mkFPEqualImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPtoFPImpl(From, To, R);
    return mkFPtoFPImpl(From, To, R);
  }

  virtual SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkSBVtoFPImpl(From, To, R);
    return mkSBVtoFPImpl(From, To, R);
  }

  virtual SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkUBVtoFPImpl(From, To, R);
    return mkUBVtoFPImpl(From, To, R);
  }

  virtual SMTExprRef mkFPtoSBV(const SMTExprRef &From,
                               unsigned ToWidth) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPtoSBVImpl(From, ToWidth);
    return mkFPtoSBVImpl(From, ToWidth);
  }

  virtual SMTExprRef mkFPtoUBV(const SMTExprRef &From,
                               unsigned ToWidth) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPtoUBVImpl(From, ToWidth);
    return mkFPtoUBVImpl(From, ToWidth);
  }

  virtual SMTExprRef mkFPtoIntegral(const SMTExprRef &From,
                                    RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFPtoIntegralImpl(From, R);
    return mkFPtoIntegralImpl(From, R);
  }

  virtual float getFloat(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::getFloatImpl(Exp);
    return getFloatImpl(Exp);
  }

  virtual double getDouble(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::getDoubleImpl(Exp);
    return getDoubleImpl(Exp);
  }

  virtual bool getInterpretation(const SMTExprRef &Exp, float &Float) override {
    if (useCamadaFP)
      return SMTFPSolver::getInterpretationImpl(Exp, Float);
    return getInterpretationImpl(Exp, Float);
  }

  virtual bool getInterpretation(const SMTExprRef &Exp,
                                 double &Double) override {
    if (useCamadaFP)
      return SMTFPSolver::getInterpretationImpl(Exp, Double);
    return getInterpretationImpl(Exp, Double);
  }

  virtual SMTExprRef mkFloat(const float Float) override {
    if (useCamadaFP)
      return SMTFPSolver::mkFloatImpl(Float);
    return mkFloatImpl(Float);
  }

  virtual SMTExprRef mkDouble(const double Double) override {
    if (useCamadaFP)
      return SMTFPSolver::mkDoubleImpl(Double);
    return mkDoubleImpl(Double);
  }

  virtual SMTExprRef mkRoundingMode(const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolver::mkRoundingModeImpl(R);
    return mkRoundingModeImpl(R);
  }

  virtual SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) override {
    if (useCamadaFP)
      return SMTFPSolver::mkNaNImpl(Sgn, ExpWidth, SigWidth);
    return mkNaNImpl(Sgn, ExpWidth, SigWidth);
  }

  virtual SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) override {
    if (useCamadaFP)
      return SMTFPSolver::mkInfImpl(Sgn, ExpWidth, SigWidth);
    return mkInfImpl(Sgn, ExpWidth, SigWidth);
  }

  virtual SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp,
                                  const SMTSortRef &To) override {
    if (useCamadaFP)
      return SMTFPSolver::mkBVToIEEEFPImpl(Exp, To);
    return mkBVToIEEEFPImpl(Exp, To);
  }

  virtual SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolver::mkIEEEFPToBVImpl(Exp);
    return mkIEEEFPToBVImpl(Exp);
  }

protected:
  virtual SMTSortRef getRoundingModeSortImpl();

  virtual SMTSortRef getFloatSortImpl(const unsigned ExpWidth,
                                      const unsigned SigWidth);

  virtual SMTExprRef mkFPAbsImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPNegImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsInfiniteImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsNaNImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsDenormalImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsNormalImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsZeroImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const RoundingMode R);

  virtual SMTExprRef mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const RoundingMode R);

  virtual SMTExprRef mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const RoundingMode R);

  virtual SMTExprRef mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const RoundingMode R);

  virtual SMTExprRef mkFPSqrtImpl(const SMTExprRef &Exp, const RoundingMode R);

  virtual SMTExprRef mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                 const SMTExprRef &Z, const RoundingMode R);

  virtual SMTExprRef mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                  const RoundingMode R);

  virtual SMTExprRef mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const RoundingMode R);

  virtual SMTExprRef mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const RoundingMode R);

  virtual SMTExprRef mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoIntegralImpl(const SMTExprRef &From, RoundingMode R);

  virtual float getFloatImpl(const SMTExprRef &Exp);

  virtual double getDoubleImpl(const SMTExprRef &Exp);

  virtual bool getInterpretationImpl(const SMTExprRef &Exp, float &Float);

  virtual bool getInterpretationImpl(const SMTExprRef &Exp, double &Double);

  virtual SMTExprRef mkFloatImpl(const float Float);

  virtual SMTExprRef mkDoubleImpl(const double Double);

  virtual SMTExprRef mkRoundingModeImpl(const RoundingMode R);

  virtual SMTExprRef mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                      const SMTSortRef &To);

  virtual SMTExprRef mkIEEEFPToBVImpl(const SMTExprRef &Exp);

  SMTExprRef mkToBV(SMTExprRef x, bool is_signed, unsigned int width);

  SMTExprRef round(SMTExprRef &R, SMTExprRef &Sgn, SMTExprRef &Sig,
                   SMTExprRef &Exp, unsigned EWidth, unsigned SWidth);
};

} // namespace camada

#endif