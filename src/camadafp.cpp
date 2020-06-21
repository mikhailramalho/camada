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

#include <cassert>
#include <cmath>
#include <cstring>

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

static inline SMTExprRef mkBias(SMTSolver &S, SMTExprRef e) {
  unsigned int ExpWidth = e->Sort->getBitvectorSortSize();

  SMTExprRef bias = S.mkBitvector(power2m1(ExpWidth - 1, false), ExpWidth);
  return S.mkBVAdd(e, bias);
}

static inline SMTExprRef mkUnbias(SMTSolver &S, SMTExprRef &Src) {
  unsigned EWidth = Src->Sort->getBitvectorSortSize();

  SMTExprRef e_plus_one = S.mkBVAdd(Src, S.mkBitvector(1, EWidth));

  SMTExprRef leading = S.mkBVExtract(EWidth - 1, EWidth - 1, e_plus_one);
  SMTExprRef n_leading = S.mkBVNot(leading);
  SMTExprRef rest = S.mkBVExtract(EWidth - 2, 0, e_plus_one);
  return S.mkBVConcat(n_leading, rest);
}

static inline SMTExprRef mkLeadingZeros(SMTSolver &S, SMTExprRef &Src,
                                        unsigned int MaxBits) {
  std::size_t bv_sz = Src->Sort->getBitvectorSortSize();
  if (bv_sz == 0)
    return S.mkBitvector(0, MaxBits);

  if (bv_sz == 1) {
    SMTExprRef nil_1 = S.mkBitvector(0, 1);
    SMTExprRef one_m = S.mkBitvector(1, MaxBits);
    SMTExprRef nil_m = S.mkBitvector(0, MaxBits);

    SMTExprRef eq = S.mkEqual(Src, nil_1);
    return S.mkIte(eq, one_m, nil_m);
  }

  SMTExprRef H = S.mkBVExtract(bv_sz - 1, bv_sz / 2, Src);
  SMTExprRef L = S.mkBVExtract(bv_sz / 2 - 1, 0, Src);

  unsigned H_size = H->Sort->getBitvectorSortSize();

  SMTExprRef lzH = mkLeadingZeros(S, H, MaxBits); /* recursive! */
  SMTExprRef lzL = mkLeadingZeros(S, L, MaxBits);

  SMTExprRef nil_h = S.mkBitvector(0, H_size);
  SMTExprRef H_is_zero = S.mkEqual(H, nil_h);

  SMTExprRef h_m = S.mkBitvector(H_size, MaxBits);
  SMTExprRef sum = S.mkBVAdd(h_m, lzL);
  return S.mkIte(H_is_zero, sum, lzH);
}

static inline SMTExprRef mkIsRM(SMTSolver &S, SMTExprRef &RME,
                                const RoundingMode R) {
  SMTExprRef RNum = S.mkBitvector(static_cast<int64_t>(R), 3);
  switch (R) {
  default:
    camada::abortWithMessage("Unsupported floating-point semantics.");
  case RoundingMode::ROUND_TO_EVEN:
  case RoundingMode::ROUND_TO_AWAY:
  case RoundingMode::ROUND_TO_PLUS_INF:
  case RoundingMode::ROUND_TO_MINUS_INF:
  case RoundingMode::ROUND_TO_ZERO:
    return S.mkEqual(RME, RNum);
  }
}

static inline SMTExprRef mkRoundingDecision(SMTSolver &S, SMTExprRef &R,
                                            SMTExprRef &Sgn, SMTExprRef &Last,
                                            SMTExprRef &Round,
                                            SMTExprRef &Sticky) {
  SMTExprRef last_or_sticky = S.mkBVOr(Last, Sticky);
  SMTExprRef round_or_sticky = S.mkBVOr(Round, Sticky);

  SMTExprRef not_round = S.mkBVNot(Round);
  SMTExprRef not_lors = S.mkBVNot(last_or_sticky);
  SMTExprRef not_rors = S.mkBVNot(round_or_sticky);
  SMTExprRef not_sgn = S.mkBVNot(Sgn);

  SMTExprRef inc_teven = S.mkBVNot(S.mkBVOr(not_round, not_lors));
  SMTExprRef inc_taway = Round;
  SMTExprRef inc_pos = S.mkBVNot(S.mkBVOr(Sgn, not_rors));
  SMTExprRef inc_neg = S.mkBVNot(S.mkBVOr(not_sgn, not_rors));

  SMTExprRef nil_1 = S.mkBitvector(0, 1);

  SMTExprRef rm_is_to_neg = mkIsRM(S, R, RoundingMode::ROUND_TO_MINUS_INF);
  SMTExprRef rm_is_to_pos = mkIsRM(S, R, RoundingMode::ROUND_TO_PLUS_INF);
  SMTExprRef rm_is_away = mkIsRM(S, R, RoundingMode::ROUND_TO_AWAY);
  SMTExprRef rm_is_even = mkIsRM(S, R, RoundingMode::ROUND_TO_EVEN);

  SMTExprRef inc_c4 = S.mkIte(rm_is_to_neg, inc_neg, nil_1);
  SMTExprRef inc_c3 = S.mkIte(rm_is_to_pos, inc_pos, inc_c4);
  SMTExprRef inc_c2 = S.mkIte(rm_is_away, inc_taway, inc_c3);
  return S.mkIte(rm_is_even, inc_teven, inc_c2);
}

static inline void unpack(SMTSolver &S, SMTExprRef &Src, SMTExprRef &Sgn,
                          SMTExprRef &Sig, SMTExprRef &Exp, SMTExprRef &LZ,
                          bool Normalize) {
  unsigned SWidth = Src->Sort->getFloatSignificandSize();
  unsigned EWidth = Src->Sort->getFloatExponentSize();

  // Extract parts
  Sgn = extractSgn(S, Src);
  Exp = extractExp(S, Src);
  Sig = extractSig(S, Src);

  assert(Sgn->Sort->getBitvectorSortSize() == 1);
  assert(Exp->Sort->getBitvectorSortSize() == EWidth);
  assert(Sig->Sort->getBitvectorSortSize() == SWidth - 1);

  SMTExprRef is_normal = S.mkFPIsNormal(Src);
  SMTExprRef normal_sig = S.mkBVConcat(S.mkBitvector(1, 1), Sig);
  SMTExprRef normal_exp = mkUnbias(S, Exp);

  SMTExprRef denormal_sig = S.mkBVZeroExt(1, Sig);
  SMTExprRef denormal_exp = S.mkBitvector(1, EWidth);
  denormal_exp = mkUnbias(S, denormal_exp);

  SMTExprRef zero_e = S.mkBitvector(0, EWidth);
  if (Normalize) {
    SMTExprRef zero_s = S.mkBitvector(0, SWidth);
    SMTExprRef is_sig_zero = S.mkEqual(zero_s, denormal_sig);

    SMTExprRef lz_d = mkLeadingZeros(S, denormal_sig, EWidth);

    SMTExprRef norm_or_zero = S.mkOr(is_normal, is_sig_zero);
    LZ = S.mkIte(norm_or_zero, zero_e, lz_d);

    SMTExprRef shift = S.mkIte(is_sig_zero, zero_e, LZ);
    assert(shift->Sort->getBitvectorSortSize() == EWidth);

    if (EWidth <= SWidth) {
      SMTExprRef q = S.mkBVZeroExt(SWidth - EWidth, shift);
      denormal_sig = S.mkBVShl(denormal_sig, q);
    } else {
      // the maximum shift is `SWidth', because after that the mantissa
      // would be zero anyways. So we can safely cut the shift variable down,
      // as long as we check the higher bits.
      SMTExprRef zero_ems = S.mkBitvector(0, EWidth - SWidth);
      SMTExprRef SWidth_s = S.mkBitvector(SWidth, SWidth);
      SMTExprRef sh = S.mkBVExtract(EWidth - 1, SWidth, shift);
      SMTExprRef is_sh_zero = S.mkEqual(zero_ems, sh);
      SMTExprRef short_shift = S.mkBVExtract(SWidth - 1, 0, shift);
      SMTExprRef sl = S.mkIte(is_sh_zero, short_shift, SWidth_s);
      denormal_sig = S.mkBVShl(denormal_sig, sl);
    }
  } else
    LZ = zero_e;

  Sig = S.mkIte(is_normal, normal_sig, denormal_sig);
  Exp = S.mkIte(is_normal, normal_exp, denormal_exp);

  assert(Sgn->Sort->getBitvectorSortSize() == 1);
  assert(Exp->Sort->getBitvectorSortSize() == EWidth);
  assert(Sig->Sort->getBitvectorSortSize() == SWidth);
}

SMTSortRef SMTFPSolverBase::getRoundingModeSortImpl() {
  return getRoundingModeSort();
}

SMTSortRef SMTFPSolverBase::getFloatSortImpl(const unsigned ExpWidth,
                                             const unsigned SigWidth) {
  return getFloatSort(ExpWidth, SigWidth);
}

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
                                        const RoundingMode R) {
  return mkFPAdd(LHS, mkFPNeg(RHS), R);
}

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

template <typename FPType, typename IntType>
static inline IntType FPasInt(const FPType FP) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage(sizeof(FPType) == sizeof(IntType),
                               "Cannot convert int to floating-point");

  IntType FPAsInt;
  memcpy(&FPAsInt, &FP, sizeof(FPType));
  return FPAsInt;
}

SMTExprRef SMTFPSolverBase::mkFloatImpl(const float Float) {
  return mkBitvector(FPasInt<float, int32_t>(Float), 32);
}

SMTExprRef SMTFPSolverBase::mkDoubleImpl(const double Double) {
  return mkBitvector(FPasInt<double, int64_t>(Double), 64);
}

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

SMTExprRef SMTFPSolverBase::round(SMTExprRef &R, SMTExprRef &Sgn,
                                  SMTExprRef &Sig, SMTExprRef &Exp,
                                  unsigned EWidth, unsigned SWidth) {
  // Assumptions: sig is of the form f[-1:0] . f[1:SWidth-1]
  // [guard,round,sticky],
  // i.e., it has 2 + (SWidth-1) + 3 = SWidth + 4 bits, where the first one is
  // in sgn. Furthermore, note that sig is an unsigned bit-vector, while exp is
  // signed.

  assert(R->Sort->getBitvectorSortSize() == 3);
  assert(Sgn->Sort->getBitvectorSortSize() == 1);
  assert(Sig->Sort->getBitvectorSortSize() >= 5);
  assert(Exp->Sort->getBitvectorSortSize() >= 4);

  assert(Sig->Sort->getBitvectorSortSize() == SWidth + 4);
  assert(Exp->Sort->getBitvectorSortSize() == EWidth + 2);

  SMTExprRef e_min = mkMinExp(*this, EWidth);
  SMTExprRef e_max = mkMaxExp(*this, EWidth);

  SMTExprRef one_1 = mkBitvector(1, 1);
  SMTExprRef h_exp = mkBVExtract(EWidth + 1, EWidth + 1, Exp);
  SMTExprRef sh_exp = mkBVExtract(EWidth, EWidth, Exp);
  SMTExprRef th_exp = mkBVExtract(EWidth - 1, EWidth - 1, Exp);
  SMTExprRef e3 = mkEqual(h_exp, one_1);
  SMTExprRef e2 = mkEqual(sh_exp, one_1);
  SMTExprRef e1 = mkEqual(th_exp, one_1);
  SMTExprRef e21 = mkOr(e2, e1);
  SMTExprRef ne3 = mkNot(e3);
  SMTExprRef e_top_three = mkAnd(ne3, e21);

  SMTExprRef ext_emax = mkBVZeroExt(2, e_max);
  SMTExprRef t_sig = mkBVExtract(SWidth + 3, SWidth + 3, Sig);
  SMTExprRef e_eq_emax = mkEqual(ext_emax, Exp);
  SMTExprRef sigm1 = mkEqual(t_sig, one_1);
  SMTExprRef e_eq_emax_and_sigm1 = mkAnd(e_eq_emax, sigm1);
  SMTExprRef OVF1 = mkOr(e_top_three, e_eq_emax_and_sigm1);

  // CMW: is this always large enough?
  SMTExprRef lz = mkLeadingZeros(*this, Sig, EWidth + 2);

  SMTExprRef t = mkBVAdd(Exp, mkBitvector(1, EWidth + 2));
  t = mkBVSub(t, lz);
  t = mkBVSub(t, mkBVSignExt(2, e_min));
  SMTExprRef TINY = mkBVSle(t, mkBitvector(ULLONG_MAX, EWidth + 2));

  SMTExprRef beta = mkBVAdd(mkBVSub(Exp, lz), mkBitvector(1, EWidth + 2));

  SMTExprRef sigma_add = mkBVSub(Exp, mkBVSignExt(2, e_min));
  sigma_add = mkBVAdd(sigma_add, mkBitvector(1, EWidth + 2));
  SMTExprRef sigma = mkIte(TINY, sigma_add, lz);

  // Normalization shift
  std::size_t sig_size = Sig->Sort->getBitvectorSortSize();
  assert(sig_size == SWidth + 4);
  assert(sigma->Sort->getBitvectorSortSize() == EWidth + 2);
  std::size_t sigma_size = EWidth + 2;

  SMTExprRef sigma_neg = mkBVNeg(sigma);
  SMTExprRef sigma_cap = mkBitvector(SWidth + 2, sigma_size);
  SMTExprRef sigma_le_cap = mkBVUle(sigma_neg, sigma_cap);
  SMTExprRef sigma_neg_capped = mkIte(sigma_le_cap, sigma_neg, sigma_cap);
  SMTExprRef sigma_lt_zero =
      mkBVSle(sigma, mkBitvector(ULLONG_MAX, sigma_size));

  SMTExprRef sig_ext = mkBVConcat(Sig, mkBitvector(0, sig_size));
  SMTExprRef rs_sig = mkBVLshr(
      sig_ext, mkBVZeroExt(2 * sig_size - sigma_size, sigma_neg_capped));
  SMTExprRef ls_sig =
      mkBVShl(sig_ext, mkBVZeroExt(2 * sig_size - sigma_size, sigma));
  SMTExprRef big_sh_sig = mkIte(sigma_lt_zero, rs_sig, ls_sig);
  assert(big_sh_sig->Sort->getBitvectorSortSize() == 2 * sig_size);

  std::size_t sig_extract_low_bit = (2 * sig_size - 1) - (SWidth + 2) + 1;
  Sig = mkBVExtract(2 * sig_size - 1, sig_extract_low_bit, big_sh_sig);
  assert(Sig->Sort->getBitvectorSortSize() == SWidth + 2);

  SMTExprRef sticky =
      mkBVRedOr(mkBVExtract(sig_extract_low_bit - 1, 0, big_sh_sig));

  // put the sticky bit into the significand.
  SMTExprRef ext_sticky = mkBVZeroExt(SWidth + 1, sticky);
  Sig = mkBVOr(Sig, ext_sticky);
  assert(Sig->Sort->getBitvectorSortSize() == SWidth + 2);

  SMTExprRef ext_emin = mkBVZeroExt(2, e_min);
  Exp = mkIte(TINY, ext_emin, beta);

  // Significand rounding
  sticky = mkBVExtract(0, 0, Sig); // new sticky bit!
  SMTExprRef round = mkBVExtract(1, 1, Sig);
  SMTExprRef last = mkBVExtract(2, 2, Sig);

  Sig = mkBVExtract(SWidth + 1, 2, Sig);

  SMTExprRef inc = mkRoundingDecision(*this, R, Sgn, last, round, sticky);
  assert(inc->Sort->getBitvectorSortSize() == 1);

  Sig = mkBVAdd(mkBVZeroExt(1, Sig), mkBVZeroExt(SWidth, inc));

  // Post normalization
  assert(Sig->Sort->getBitvectorSortSize() == SWidth + 1);
  t_sig = mkBVExtract(SWidth, SWidth, Sig);
  SMTExprRef SIGovf = mkEqual(t_sig, one_1);

  SMTExprRef hallbut1_sig = mkBVExtract(SWidth, 1, Sig);
  SMTExprRef lallbut1_sig = mkBVExtract(SWidth - 1, 0, Sig);
  Sig = mkIte(SIGovf, hallbut1_sig, lallbut1_sig);

  assert(Exp->Sort->getBitvectorSortSize() == EWidth + 2);

  SMTExprRef exp_p1 = mkBVAdd(Exp, mkBitvector(1, EWidth + 2));
  Exp = mkIte(SIGovf, exp_p1, Exp);

  assert(Sig->Sort->getBitvectorSortSize() == SWidth);
  assert(Exp->Sort->getBitvectorSortSize() == EWidth + 2);
  assert(e_max->Sort->getBitvectorSortSize() == EWidth);

  // Exponent adjustment and rounding
  SMTExprRef biased_exp = mkBias(*this, mkBVExtract(EWidth - 1, 0, Exp));

  // AdjustExp
  assert(OVF1->Sort->isBooleanSort());

  SMTExprRef exp_redand = mkBVRedAnd(biased_exp);
  SMTExprRef preOVF2 = mkEqual(exp_redand, one_1);
  SMTExprRef OVF2 = mkAnd(SIGovf, preOVF2);
  SMTExprRef pem2m1 = mkBitvector(power2m1(EWidth - 2, false), EWidth);
  biased_exp = mkIte(OVF2, pem2m1, biased_exp);
  SMTExprRef OVF = mkOr(OVF1, OVF2);

  assert(OVF2->Sort->isBooleanSort());
  assert(OVF->Sort->isBooleanSort());

  // ExpRnd
  SMTExprRef top_exp = mkTopExp(*this, EWidth);
  SMTExprRef bot_exp = mkBotExp(*this, EWidth);

  SMTExprRef nil_1 = mkBitvector(0, 1);

  SMTExprRef rm_is_to_zero = mkIsRM(*this, R, RoundingMode::ROUND_TO_ZERO);
  SMTExprRef rm_is_to_neg = mkIsRM(*this, R, RoundingMode::ROUND_TO_MINUS_INF);
  SMTExprRef rm_is_to_pos = mkIsRM(*this, R, RoundingMode::ROUND_TO_PLUS_INF);
  SMTExprRef rm_zero_or_neg = mkOr(rm_is_to_zero, rm_is_to_neg);
  SMTExprRef rm_zero_or_pos = mkOr(rm_is_to_zero, rm_is_to_pos);

  SMTExprRef zero1 = mkBitvector(0, 1);
  SMTExprRef sgn_is_zero = mkEqual(Sgn, zero1);

  SMTExprRef max_sig = mkBitvector(power2m1(SWidth - 1, false), SWidth - 1);
  SMTExprRef max_exp = mkBVConcat(
      mkBitvector(power2m1(EWidth - 1, false), EWidth - 1), mkBitvector(0, 1));
  SMTExprRef inf_sig = mkBitvector(0, SWidth - 1);
  SMTExprRef inf_exp = top_exp;

  SMTExprRef max_inf_exp_neg = mkIte(rm_zero_or_pos, max_exp, inf_exp);
  SMTExprRef max_inf_exp_pos = mkIte(rm_zero_or_neg, max_exp, inf_exp);
  SMTExprRef ovfl_exp = mkIte(sgn_is_zero, max_inf_exp_pos, max_inf_exp_neg);
  t_sig = mkBVExtract(SWidth - 1, SWidth - 1, Sig);
  SMTExprRef n_d_check = mkEqual(t_sig, nil_1);
  SMTExprRef n_d_exp = mkIte(n_d_check, bot_exp /* denormal */, biased_exp);
  Exp = mkIte(OVF, ovfl_exp, n_d_exp);

  SMTExprRef max_inf_sig_neg = mkIte(rm_zero_or_pos, max_sig, inf_sig);
  SMTExprRef max_inf_sig_pos = mkIte(rm_zero_or_neg, max_sig, inf_sig);
  SMTExprRef ovfl_sig = mkIte(sgn_is_zero, max_inf_sig_pos, max_inf_sig_neg);
  SMTExprRef rest_sig = mkBVExtract(SWidth - 2, 0, Sig);
  Sig = mkIte(OVF, ovfl_sig, rest_sig);

  assert(Sgn->Sort->getBitvectorSortSize() == 1);
  assert(Sig->Sort->getBitvectorSortSize() == SWidth - 1);
  assert(Exp->Sort->getBitvectorSortSize() == EWidth);

  return mkBVToIEEEFP(mkBVConcat(Sgn, mkBVConcat(Exp, Sig)),
                      getFloatSort(EWidth, SWidth - 1));
}
