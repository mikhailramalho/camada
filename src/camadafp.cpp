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
                                       const SMTExprRef &RHS) {
  SMTExprRef x_is_nan = mkFPIsNaN(LHS);
  SMTExprRef y_is_nan = mkFPIsNaN(RHS);
  SMTExprRef c1 = mkOr(x_is_nan, y_is_nan);
  SMTExprRef x_is_zero = mkFPIsZero(LHS);
  SMTExprRef y_is_zero = mkFPIsZero(RHS);
  SMTExprRef c2 = mkAnd(x_is_zero, y_is_zero);

  SMTExprRef x_sgn = extractSgn(*this, LHS);
  SMTExprRef x_sig = extractSig(*this, LHS);
  SMTExprRef x_exp = extractExp(*this, LHS);

  SMTExprRef y_sgn = extractSgn(*this, RHS);
  SMTExprRef y_sig = extractSig(*this, RHS);
  SMTExprRef y_exp = extractExp(*this, RHS);

  SMTExprRef one_1 = mkBitvector(1, 1);
  SMTExprRef nil_1 = mkBitvector(0, 1);
  SMTExprRef c3 = mkEqual(x_sgn, one_1);

  SMTExprRef y_sgn_eq_0 = mkEqual(y_sgn, nil_1);
  SMTExprRef y_lt_x_exp = mkBVUlt(y_exp, x_exp);
  SMTExprRef y_lt_x_sig = mkBVUlt(y_sig, x_sig);
  SMTExprRef y_eq_x_exp = mkEqual(y_exp, x_exp);
  SMTExprRef y_le_x_sig_exp = mkAnd(y_eq_x_exp, y_lt_x_sig);
  SMTExprRef t3_or = mkOr(y_lt_x_exp, y_le_x_sig_exp);
  SMTExprRef t3 = mkIte(y_sgn_eq_0, mkBoolean(true), t3_or);

  SMTExprRef y_sgn_eq_1 = mkEqual(y_sgn, one_1);
  SMTExprRef x_lt_y_exp = mkBVUlt(x_exp, y_exp);
  SMTExprRef x_eq_y_exp = mkEqual(x_exp, y_exp);
  SMTExprRef x_lt_y_sig = mkBVUlt(x_sig, y_sig);
  SMTExprRef x_le_y_sig_exp = mkAnd(x_eq_y_exp, x_lt_y_sig);
  SMTExprRef t4_or = mkOr(x_lt_y_exp, x_le_y_sig_exp);
  SMTExprRef t4 = mkIte(y_sgn_eq_1, mkBoolean(false), t4_or);

  SMTExprRef c3t3t4 = mkIte(c3, t3, t4);
  SMTExprRef c2else = mkIte(c2, mkBoolean(false), c3t3t4);
  return mkIte(c1, mkBoolean(false), c2else);
}

SMTExprRef SMTFPSolverBase::mkFPLeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  SMTExprRef lt = mkFPLt(LHS, RHS);
  SMTExprRef eq = mkFPEqual(LHS, RHS);
  return mkOr(lt, eq);
}

SMTExprRef SMTFPSolverBase::mkFPEqualImpl(const SMTExprRef &LHS,
                                          const SMTExprRef &RHS) {
  // +0 and -0 should return true
  SMTExprRef isZeroLHS = mkFPIsZero(LHS);
  SMTExprRef isZeroRHS = mkFPIsZero(RHS);
  SMTExprRef bothZero = mkAnd(isZeroLHS, isZeroRHS);

  // Check if they are NaN
  SMTExprRef isNanLHS = mkFPIsNaN(LHS);
  SMTExprRef isNanRHS = mkFPIsNaN(RHS);
  SMTExprRef nan = mkOr(isNanLHS, isNanRHS);

  // Otherwise compare them bitwise
  SMTExprRef are_equal = mkEqual(LHS, RHS);

  // They are equal if they are either +0 and -0 (and vice-versa) or bitwise
  // equal and neither is NaN
  return mkAnd(mkOr(bothZero, are_equal), mkNot(nan));
}

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

SMTExprRef SMTFPSolverBase::mkRoundingModeImpl(const RoundingMode R) {
  return mkBitvector(static_cast<int64_t>(R), 3);
}

SMTExprRef SMTFPSolverBase::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                      const unsigned SigWidth) {
  // we always create the same NaN: sgn = Sgn, exp = all 1, sig = 0...01
  SMTExprRef top_exp = mkTopExp(*this, ExpWidth);
  return mkBVToIEEEFP(
      mkBVConcat(mkBitvector(Sgn, 1),
                 mkBVConcat(top_exp, mkBitvector(1, SigWidth - 1))),
      getFloatSort(ExpWidth, SigWidth - 1));
}

SMTExprRef SMTFPSolverBase::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                      const unsigned SigWidth) {
  SMTExprRef top_exp = mkTopExp(*this, ExpWidth);
  return mkBVToIEEEFP(
      mkBVConcat(mkBitvector(Sgn, 1),
                 mkBVConcat(top_exp, mkBitvector(0, SigWidth - 1))),
      getFloatSort(ExpWidth, SigWidth - 1));
}

SMTExprRef SMTFPSolverBase::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                             const SMTSortRef &To) {
  Exp->Sort = To;
  return Exp;
}

SMTExprRef SMTFPSolverBase::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  // Do nothing, it's already a bitvector
  return Exp;
}
