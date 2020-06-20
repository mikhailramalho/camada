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

class SMTFPSolverBase : public SMTSolver {
public:
  SMTFPSolverBase() = default;
  ~SMTFPSolverBase() = default;

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

  virtual SMTExprRef mkBVToIEEEFPImpl(SMTExprRef Exp, SMTSortRef To);

  virtual SMTExprRef mkIEEEFPToBVImpl(SMTExprRef Exp);
};

template <typename SMTSolverImpl> class SMTFPSolver : public SMTFPSolverBase {
public:
  SMTFPSolver() = default;
  virtual ~SMTFPSolver() = default;

  virtual SMTSortRef getRoundingModeSort() override {
    if (useCamadaFP)
      return SMTFPSolverBase::getRoundingModeSortImpl();
    return getRoundingModeSortImpl();
  }

  virtual SMTSortRef getFloatSort(const unsigned ExpWidth,
                                  const unsigned SigWidth) override {
    if (useCamadaFP)
      return SMTFPSolverBase::getFloatSortImpl(ExpWidth, SigWidth);
    return getFloatSortImpl(ExpWidth, SigWidth);
  }

  virtual SMTExprRef mkFPAbs(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPAbsImpl(Exp);
    return mkFPAbsImpl(Exp);
  }

  virtual SMTExprRef mkFPNeg(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPNegImpl(Exp);
    return mkFPNegImpl(Exp);
  }

  virtual SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPIsInfiniteImpl(Exp);
    return mkFPIsInfiniteImpl(Exp);
  }

  virtual SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPIsNaNImpl(Exp);
    return mkFPIsNaNImpl(Exp);
  }

  virtual SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPIsDenormalImpl(Exp);
    return mkFPIsDenormalImpl(Exp);
  }

  virtual SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPIsNormalImpl(Exp);
    return mkFPIsNormalImpl(Exp);
  }

  virtual SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPIsZeroImpl(Exp);
    return mkFPIsZeroImpl(Exp);
  }

  virtual SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPMulImpl(LHS, RHS, R);
    return mkFPMulImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPDivImpl(LHS, RHS, R);
    return mkFPDivImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPRem(const SMTExprRef &LHS,
                             const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPRemImpl(LHS, RHS);
    return mkFPRemImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPAddImpl(LHS, RHS, R);
    return mkFPAddImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPSubImpl(LHS, RHS, R);
    return mkFPSubImpl(LHS, RHS, R);
  }

  virtual SMTExprRef mkFPSqrt(const SMTExprRef &Exp,
                              const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPSqrtImpl(Exp, R);
    return mkFPSqrtImpl(Exp, R);
  }

  virtual SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z,
                             const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPFMAImpl(X, Y, Z, R);
    return mkFPFMAImpl(X, Y, Z, R);
  };

  virtual SMTExprRef mkFPLt(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPLtImpl(LHS, RHS);
    return mkFPLtImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPLe(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPLeImpl(LHS, RHS);
    return mkFPLeImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPEqualImpl(LHS, RHS);
    return mkFPEqualImpl(LHS, RHS);
  }

  virtual SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPtoFPImpl(From, To, R);
    return mkFPtoFPImpl(From, To, R);
  }

  virtual SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkSBVtoFPImpl(From, To, R);
    return mkSBVtoFPImpl(From, To, R);
  }

  virtual SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkUBVtoFPImpl(From, To, R);
    return mkUBVtoFPImpl(From, To, R);
  }

  virtual SMTExprRef mkFPtoSBV(const SMTExprRef &From,
                               unsigned ToWidth) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPtoSBVImpl(From, ToWidth);
    return mkFPtoSBVImpl(From, ToWidth);
  }

  virtual SMTExprRef mkFPtoUBV(const SMTExprRef &From,
                               unsigned ToWidth) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPtoUBVImpl(From, ToWidth);
    return mkFPtoUBVImpl(From, ToWidth);
  }

  virtual SMTExprRef mkFPtoIntegral(const SMTExprRef &From,
                                    RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFPtoIntegralImpl(From, R);
    return mkFPtoIntegralImpl(From, R);
  }

  virtual float getFloat(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::getFloatImpl(Exp);
    return getFloatImpl(Exp);
  }

  virtual double getDouble(const SMTExprRef &Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::getDoubleImpl(Exp);
    return getDoubleImpl(Exp);
  }

  virtual bool getInterpretation(const SMTExprRef &Exp, float &Float) override {
    if (useCamadaFP)
      return SMTFPSolverBase::getInterpretationImpl(Exp, Float);
    return getInterpretationImpl(Exp, Float);
  }
  virtual bool getInterpretation(const SMTExprRef &Exp,
                                 double &Double) override {
    if (useCamadaFP)
      return SMTFPSolverBase::getInterpretationImpl(Exp, Double);
    return getInterpretationImpl(Exp, Double);
  }
  virtual SMTExprRef mkFloat(const float Float) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkFloatImpl(Float);
    return mkFloatImpl(Float);
  }

  virtual SMTExprRef mkDouble(const double Double) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkDoubleImpl(Double);
    return mkDoubleImpl(Double);
  }

  virtual SMTExprRef mkRoundingMode(const RoundingMode R) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkRoundingModeImpl(R);
    return mkRoundingModeImpl(R);
  }

  virtual SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkNaNImpl(Sgn, ExpWidth, SigWidth);
    return mkNaNImpl(Sgn, ExpWidth, SigWidth);
  }

  virtual SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkInfImpl(Sgn, ExpWidth, SigWidth);
    return mkInfImpl(Sgn, ExpWidth, SigWidth);
  }

  virtual SMTExprRef mkBVToIEEEFP(SMTExprRef Exp, SMTSortRef To) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkBVToIEEEFPImpl(Exp, To);
    return mkBVToIEEEFPImpl(Exp, To);
  }

  virtual SMTExprRef mkIEEEFPToBV(SMTExprRef Exp) override {
    if (useCamadaFP)
      return SMTFPSolverBase::mkIEEEFPToBVImpl(Exp);
    return mkIEEEFPToBVImpl(Exp);
  }
};

} // namespace camada

#endif