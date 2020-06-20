/**************************************************************************
 *
 * Licensed to the Apache Software Foundation Impl(ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 Impl(the
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

#include <cmath>

#include "camadafp.h"

using namespace camada;

static inline SMTExprRef extractSgn(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkBVExtract(Exp->Sort->getBitvectorSortSize() - 1,
                       Exp->Sort->getBitvectorSortSize() - 1, Exp);
}

static inline SMTExprRef extractExp(SMTSolver &S, const SMTExprRef &Exp) {
  unsigned int expTop = Exp->Sort->getFloatSortSize() - 2;
  unsigned int expBot = Exp->Sort->getFloatSignificandSize() - 2;
  return S.mkBVExtract(expTop, expBot + 1, Exp);
}

static inline SMTExprRef extractSig(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkBVExtract(Exp->Sort->getFloatSignificandSize() - 2, 0, Exp);
}

static inline SMTExprRef extractExpSig(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkBVExtract(Exp->Sort->getFloatSortSize() - 2, 0, Exp);
}

static inline unsigned int power2(unsigned int N, bool Negated) {
  unsigned int b = pow(2, N);
  return Negated ? -b : b;
}

static inline unsigned int power2m1(unsigned int N, bool Negated) {
  unsigned int b = pow(2, N);
  b -= 1;
  return Negated ? -b : b;
}

SMTExprRef mkMinExp(SMTSolver &S, unsigned int ExpWidth) {
  return S.mkBitvector(power2m1(ExpWidth - 1, true) + 1, ExpWidth);
}

SMTExprRef mkMaxExp(SMTSolver &S, unsigned int ExpWidth) {
  return S.mkBitvector(power2m1(ExpWidth - 1, false), ExpWidth);
}

static inline SMTExprRef mkTopExp(SMTSolver &S, unsigned int ExpWidth) {
  return S.mkBitvector(power2m1(ExpWidth, false), ExpWidth);
}

static inline SMTExprRef mkBotExp(SMTSolver &S, unsigned int ExpWidth) {
  return S.mkBitvector(0, ExpWidth);
}

SMTSortRef SMTFPSolverBase::getRoundingModeSortImpl() {}

SMTSortRef SMTFPSolverBase::getFloatSortImpl(const unsigned ExpWidth,
                                             const unsigned SigWidth) {}

SMTExprRef SMTFPSolverBase::mkFPAbsImpl(const SMTExprRef &Exp) {
  // Extract everything but the sign bit
  SMTExprRef ew_sw = extractExpSig(*this, Exp);

  // Concat that with '0'
  SMTExprRef zero = mkBitvector(0, 1);
  return mkBVToIEEEFP(mkBVConcat(zero, ew_sw), Exp->Sort);
}

SMTExprRef SMTFPSolverBase::mkFPNegImpl(const SMTExprRef &Exp) {
  // Extract everything but the sign bit
  SMTExprRef ew_sw = extractExpSig(*this, Exp);
  SMTExprRef sgn = extractSgn(*this, Exp);
  return mkBVToIEEEFP(mkBVConcat(mkBVNot(sgn), ew_sw), Exp->Sort);
}

SMTExprRef SMTFPSolverBase::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  // Extract the exponent and significand
  SMTExprRef exp = extractExp(*this, Exp);
  SMTExprRef sig = extractSig(*this, Exp);

  // exp == 1^n , sig == 0
  SMTExprRef topExp = mkTopExp(*this, exp->Sort->getBitvectorSortSize());

  SMTExprRef zero = mkBitvector(0, sig->Sort->getBitvectorSortSize());
  SMTExprRef sigIsZero = mkEqual(sig, zero);
  SMTExprRef expIsTop = mkEqual(exp, topExp);
  return mkAnd(expIsTop, sigIsZero);
}

SMTExprRef SMTFPSolverBase::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  // Extract the exponent and significand
  SMTExprRef exp = extractExp(*this, Exp);
  SMTExprRef sig = extractSig(*this, Exp);

  // exp == 1^n , sig != 0
  SMTExprRef topExp = mkTopExp(*this, exp->Sort->getBitvectorSortSize());

  SMTExprRef zero = mkBitvector(0, sig->Sort->getBitvectorSortSize());
  SMTExprRef sigIsNotZero = mkNot(mkEqual(sig, zero));
  SMTExprRef expIsTop = mkEqual(exp, topExp);
  return mkAnd(expIsTop, sigIsNotZero);
}

SMTExprRef SMTFPSolverBase::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  // Extract the exponent
  SMTExprRef exp = extractExp(*this, Exp);

  SMTExprRef zero = mkBitvector(0, exp->Sort->getBitvectorSortSize());
  SMTExprRef zExp = mkEqual(exp, zero);
  SMTExprRef isZero = mkFPIsZero(Exp);
  SMTExprRef nIsZero = mkNot(isZero);
  return mkAnd(nIsZero, zExp);
}

SMTExprRef SMTFPSolverBase::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  // Extract the exponent
  SMTExprRef exp = extractExp(*this, Exp);

  SMTExprRef isDenormal = mkFPIsDenormal(Exp);
  SMTExprRef isZero = mkFPIsZero(Exp);

  unsigned eWidth = exp->Sort->getBitvectorSortSize();
  SMTExprRef p = mkBitvector(power2m1(eWidth, false), eWidth);

  SMTExprRef isSpecial = mkEqual(exp, p);

  SMTExprRef orEx = mkOr(isSpecial, isDenormal);
  orEx = mkOr(isZero, orEx);
  return mkNot(orEx);
}

SMTExprRef SMTFPSolverBase::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  // Both -0 and 0 should return true

  // Extract everything but the sign bit
  SMTExprRef ew_sw = extractExpSig(*this, Exp);

  // Then compare it with zero of the same size
  return mkEqual(ew_sw, mkBitvector(0, Exp->Sort->getBitvectorSortSize() - 1));
}

SMTExprRef SMTFPSolverBase::mkFPMulImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPDivImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPRemImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPAddImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPSubImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPSqrtImpl(const SMTExprRef &Exp,
                                         const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPFMAImpl(const SMTExprRef &X,
                                        const SMTExprRef &Y,
                                        const SMTExprRef &Z,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPLtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPLeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPEqualImpl(const SMTExprRef &LHS,
                                          const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPtoFPImpl(const SMTExprRef &From,
                                         const SMTSortRef &To,
                                         const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkSBVtoFPImpl(const SMTExprRef &From,
                                          const SMTSortRef &To,
                                          const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkUBVtoFPImpl(const SMTExprRef &From,
                                          const SMTSortRef &To,
                                          const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPtoSBVImpl(const SMTExprRef &From,
                                          unsigned ToWidth) {}

SMTExprRef SMTFPSolverBase::mkFPtoUBVImpl(const SMTExprRef &From,
                                          unsigned ToWidth) {}

SMTExprRef SMTFPSolverBase::mkFPtoIntegralImpl(const SMTExprRef &From,
                                               RoundingMode R) {}

float SMTFPSolverBase::getFloatImpl(const SMTExprRef &Exp) {}

double SMTFPSolverBase::getDoubleImpl(const SMTExprRef &Exp) {}

bool SMTFPSolverBase::getInterpretationImpl(const SMTExprRef &Exp,
                                            float &Float) {}

bool SMTFPSolverBase::getInterpretationImpl(const SMTExprRef &Exp,
                                            double &Double) {}

SMTExprRef SMTFPSolverBase::mkFloatImpl(const float Float) {}

SMTExprRef SMTFPSolverBase::mkDoubleImpl(const double Double) {}

SMTExprRef SMTFPSolverBase::mkRoundingModeImpl(const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                      const unsigned SigWidth) {}

SMTExprRef SMTFPSolverBase::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                      const unsigned SigWidth) {}

SMTExprRef SMTFPSolverBase::mkBVToIEEEFPImpl(SMTExprRef Exp, SMTSortRef To) {}

SMTExprRef SMTFPSolverBase::mkIEEEFPToBVImpl(SMTExprRef Exp) {}
