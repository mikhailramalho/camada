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

#include "camadafp.h"
#include "camadautils.h"

#include <cassert>
#include <cmath>
#include <cstring>

using namespace camada;

static inline SMTExprRef extractSgn(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkBVExtract(Exp->getWidth() - 1, Exp->getWidth() - 1, Exp);
}

static inline SMTExprRef extractExp(SMTSolver &S, const SMTExprRef &Exp) {
  unsigned int expTop = Exp->getWidth() - 2;
  unsigned int expBot = Exp->Sort->getFPSignificandWidth() - 2;
  return S.mkBVExtract(expTop, expBot + 1, Exp);
}

static inline SMTExprRef extractSig(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkBVExtract(Exp->Sort->getFPSignificandWidth() - 2, 0, Exp);
}

static inline SMTExprRef extractExpSig(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkBVExtract(Exp->getWidth() - 2, 0, Exp);
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
  return S.mkBVFromDec(power2m1(ExpWidth - 1, true) + 1, ExpWidth);
}

SMTExprRef mkMaxExp(SMTSolver &S, unsigned int ExpWidth) {
  return S.mkBVFromDec(power2m1(ExpWidth - 1, false), ExpWidth);
}

static inline SMTExprRef mkTopExp(SMTSolver &S, unsigned int ExpWidth) {
  return S.mkBVFromDec(power2m1(ExpWidth, false), ExpWidth);
}

static inline SMTExprRef mkBotExp(SMTSolver &S, unsigned int ExpWidth) {
  return S.mkBVFromDec(0, ExpWidth);
}

static inline SMTExprRef mkIsPos(SMTSolver &S, const SMTExprRef &Exp) {
  SMTExprRef sgn = extractSgn(S, Exp);
  SMTExprRef zero = S.mkBVFromDec(0, sgn->getWidth());
  return S.mkEqual(sgn, zero);
}

static inline SMTExprRef mkIsNeg(SMTSolver &S, SMTExprRef Exp) {
  SMTExprRef sgn = extractSgn(S, Exp);
  SMTExprRef one = S.mkBVFromDec(1, sgn->getWidth());
  return S.mkEqual(sgn, one);
}

static inline SMTExprRef mkPZero(SMTSolver &S, unsigned int EWidth,
                                 unsigned int SWidth) {
  SMTExprRef bot_exp = mkBotExp(S, EWidth);
  return S.mkBVToIEEEFP(
      S.mkBVConcat(S.mkBVFromDec(0, 1),
                   S.mkBVConcat(bot_exp, S.mkBVFromDec(0, SWidth - 1))),
      S.getFPSort(EWidth, SWidth - 1));
}

static inline SMTExprRef mkNZero(SMTSolver &S, unsigned int EWidth,
                                 unsigned int SWidth) {
  SMTExprRef bot_exp = mkBotExp(S, EWidth);
  return S.mkBVToIEEEFP(
      S.mkBVConcat(S.mkBVFromDec(1, 1),
                   S.mkBVConcat(bot_exp, S.mkBVFromDec(0, SWidth - 1))),
      S.getFPSort(EWidth, SWidth - 1));
}

static inline SMTExprRef mkPInf(SMTSolver &S, unsigned int EWidth,
                                unsigned int SWidth) {
  SMTExprRef top_exp = mkTopExp(S, EWidth);
  return S.mkBVToIEEEFP(
      S.mkBVConcat(S.mkBVFromDec(0, 1),
                   S.mkBVConcat(top_exp, S.mkBVFromDec(0, SWidth - 1))),
      S.getFPSort(EWidth, SWidth - 1));
}

static inline SMTExprRef mkNInf(SMTSolver &S, unsigned int EWidth,
                                unsigned int SWidth) {
  SMTExprRef top_exp = mkTopExp(S, EWidth);
  return S.mkBVToIEEEFP(
      S.mkBVConcat(S.mkBVFromDec(1, 1),
                   S.mkBVConcat(top_exp, S.mkBVFromDec(0, SWidth - 1))),
      S.getFPSort(EWidth, SWidth - 1));
}

static inline SMTExprRef mkIsPZero(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkAnd(S.mkFPIsZero(Exp), mkIsPos(S, Exp));
}

static inline SMTExprRef mkIsNZero(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkAnd(S.mkFPIsZero(Exp), mkIsNeg(S, Exp));
}

static inline SMTExprRef mkIsPInf(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkAnd(S.mkFPIsInfinite(Exp), mkIsPos(S, Exp));
}

static inline SMTExprRef mkIsNInf(SMTSolver &S, const SMTExprRef &Exp) {
  return S.mkAnd(S.mkFPIsInfinite(Exp), mkIsNeg(S, Exp));
}

SMTExprRef mkOne(SMTSolver &S, SMTExprRef Sgn, unsigned int EWidth,
                 unsigned int SWidth) {
  return S.mkBVToIEEEFP(
      S.mkBVConcat(
          Sgn, S.mkBVConcat(S.mkBVFromDec(power2m1(EWidth - 1, false), EWidth),
                            S.mkBVFromDec(0, SWidth - 1))),
      S.getFPSort(EWidth, SWidth - 1));
}

static inline SMTExprRef mkBias(SMTSolver &S, SMTExprRef e) {
  unsigned int ExpWidth = e->getWidth();

  SMTExprRef bias = S.mkBVFromDec(power2m1(ExpWidth - 1, false), ExpWidth);
  return S.mkBVAdd(e, bias);
}

static inline SMTExprRef mkUnbias(SMTSolver &S, SMTExprRef &Src) {
  unsigned EWidth = Src->getWidth();

  SMTExprRef e_plus_one = S.mkBVAdd(Src, S.mkBVFromDec(1, EWidth));

  SMTExprRef leading = S.mkBVExtract(EWidth - 1, EWidth - 1, e_plus_one);
  SMTExprRef n_leading = S.mkBVNot(leading);
  SMTExprRef rest = S.mkBVExtract(EWidth - 2, 0, e_plus_one);
  return S.mkBVConcat(n_leading, rest);
}

static inline SMTExprRef mkLeadingZeros(SMTSolver &S, const SMTExprRef &Src,
                                        unsigned int MaxBits) {
  std::size_t bv_sz = Src->getWidth();
  if (bv_sz == 0)
    return S.mkBVFromDec(0, MaxBits);

  if (bv_sz == 1) {
    SMTExprRef nil_1 = S.mkBVFromDec(0, 1);
    SMTExprRef one_m = S.mkBVFromDec(1, MaxBits);
    SMTExprRef nil_m = S.mkBVFromDec(0, MaxBits);

    SMTExprRef eq = S.mkEqual(Src, nil_1);
    return S.mkIte(eq, one_m, nil_m);
  }

  SMTExprRef H = S.mkBVExtract(bv_sz - 1, bv_sz / 2, Src);
  SMTExprRef L = S.mkBVExtract(bv_sz / 2 - 1, 0, Src);

  unsigned H_size = H->getWidth();

  SMTExprRef lzH = mkLeadingZeros(S, H, MaxBits); /* recursive! */
  SMTExprRef lzL = mkLeadingZeros(S, L, MaxBits);

  SMTExprRef nil_h = S.mkBVFromDec(0, H_size);
  SMTExprRef H_is_zero = S.mkEqual(H, nil_h);

  SMTExprRef h_m = S.mkBVFromDec(H_size, MaxBits);
  SMTExprRef sum = S.mkBVAdd(h_m, lzL);
  return S.mkIte(H_is_zero, sum, lzH);
}

static inline SMTExprRef mkIsRM(SMTSolver &S, const SMTExprRef &RME,
                                const RM &R) {
  SMTExprRef RNum = S.mkBVFromDec(static_cast<int64_t>(R), 3);
  switch (R) {
  default:
    camada::abortWithMessage("Unsupported floating-point semantics.");
  case RM::ROUND_TO_EVEN:
  case RM::ROUND_TO_AWAY:
  case RM::ROUND_TO_PLUS_INF:
  case RM::ROUND_TO_MINUS_INF:
  case RM::ROUND_TO_ZERO:
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

  SMTExprRef nil_1 = S.mkBVFromDec(0, 1);

  SMTExprRef rm_is_to_neg = mkIsRM(S, R, RM::ROUND_TO_MINUS_INF);
  SMTExprRef rm_is_to_pos = mkIsRM(S, R, RM::ROUND_TO_PLUS_INF);
  SMTExprRef rm_is_away = mkIsRM(S, R, RM::ROUND_TO_AWAY);
  SMTExprRef rm_is_even = mkIsRM(S, R, RM::ROUND_TO_EVEN);

  SMTExprRef inc_c4 = S.mkIte(rm_is_to_neg, inc_neg, nil_1);
  SMTExprRef inc_c3 = S.mkIte(rm_is_to_pos, inc_pos, inc_c4);
  SMTExprRef inc_c2 = S.mkIte(rm_is_away, inc_taway, inc_c3);
  return S.mkIte(rm_is_even, inc_teven, inc_c2);
}

static inline void unpack(SMTSolver &S, const SMTExprRef &Src, SMTExprRef &Sgn,
                          SMTExprRef &Sig, SMTExprRef &Exp, SMTExprRef &LZ,
                          bool Normalize) {
  unsigned SWidth = Src->Sort->getFPSignificandWidth();
  unsigned EWidth = Src->Sort->getFPExponentWidth();

  // Extract parts
  Sgn = extractSgn(S, Src);
  Exp = extractExp(S, Src);
  Sig = extractSig(S, Src);

  assert(Sgn->getWidth() == 1);
  assert(Exp->getWidth() == EWidth);
  assert(Sig->getWidth() == SWidth - 1);

  SMTExprRef is_normal = S.mkFPIsNormal(Src);
  SMTExprRef normal_sig = S.mkBVConcat(S.mkBVFromDec(1, 1), Sig);
  SMTExprRef normal_exp = mkUnbias(S, Exp);

  SMTExprRef denormal_sig = S.mkBVZeroExt(1, Sig);
  SMTExprRef denormal_exp = S.mkBVFromDec(1, EWidth);
  denormal_exp = mkUnbias(S, denormal_exp);

  SMTExprRef zero_e = S.mkBVFromDec(0, EWidth);
  if (Normalize) {
    SMTExprRef zero_s = S.mkBVFromDec(0, SWidth);
    SMTExprRef is_sig_zero = S.mkEqual(zero_s, denormal_sig);

    SMTExprRef lz_d = mkLeadingZeros(S, denormal_sig, EWidth);

    SMTExprRef norm_or_zero = S.mkOr(is_normal, is_sig_zero);
    LZ = S.mkIte(norm_or_zero, zero_e, lz_d);

    SMTExprRef shift = S.mkIte(is_sig_zero, zero_e, LZ);
    assert(shift->getWidth() == EWidth);

    if (EWidth <= SWidth) {
      SMTExprRef q = S.mkBVZeroExt(SWidth - EWidth, shift);
      denormal_sig = S.mkBVShl(denormal_sig, q);
    } else {
      // the maximum shift is `SWidth', because after that the mantissa
      // would be zero anyways. So we can safely cut the shift variable down,
      // as long as we check the higher bits.
      SMTExprRef zero_ems = S.mkBVFromDec(0, EWidth - SWidth);
      SMTExprRef SWidth_s = S.mkBVFromDec(SWidth, SWidth);
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

  assert(Sgn->getWidth() == 1);
  assert(Exp->getWidth() == EWidth);
  assert(Sig->getWidth() == SWidth);
}

SMTSortRef SMTFPSolver::getRMSortImpl() { return getBVRMSort(); }

SMTSortRef SMTFPSolver::getFPSortImpl(const unsigned ExpWidth,
                                      const unsigned SigWidth) {

  return getBVFPSort(ExpWidth, SigWidth);
}

SMTExprRef SMTFPSolver::mkFPAbsImpl(const SMTExprRef &Exp) {
  // Extract everything but the sign bit
  SMTExprRef ew_sw = extractExpSig(*this, Exp);

  // Concat that with '0'
  SMTExprRef zero = mkBVFromDec(0, 1);
  return mkBVToIEEEFP(mkBVConcat(zero, ew_sw), Exp->Sort);
}

SMTExprRef SMTFPSolver::mkFPNegImpl(const SMTExprRef &Exp) {
  // Extract everything but the sign bit
  SMTExprRef ew_sw = extractExpSig(*this, Exp);
  SMTExprRef sgn = extractSgn(*this, Exp);
  return mkBVToIEEEFP(mkBVConcat(mkBVNot(sgn), ew_sw), Exp->Sort);
}

SMTExprRef SMTFPSolver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  // Extract the exponent and significand
  SMTExprRef exp = extractExp(*this, Exp);
  SMTExprRef sig = extractSig(*this, Exp);

  // exp == 1^n , sig == 0
  SMTExprRef topExp = mkTopExp(*this, exp->getWidth());

  SMTExprRef zero = mkBVFromDec(0, sig->getWidth());
  SMTExprRef sigIsZero = mkEqual(sig, zero);
  SMTExprRef expIsTop = mkEqual(exp, topExp);
  return mkAnd(expIsTop, sigIsZero);
}

SMTExprRef SMTFPSolver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  // Extract the exponent and significand
  SMTExprRef exp = extractExp(*this, Exp);
  SMTExprRef sig = extractSig(*this, Exp);

  // exp == 1^n , sig != 0
  SMTExprRef topExp = mkTopExp(*this, exp->getWidth());

  SMTExprRef zero = mkBVFromDec(0, sig->getWidth());
  SMTExprRef sigIsNotZero = mkNot(mkEqual(sig, zero));
  SMTExprRef expIsTop = mkEqual(exp, topExp);
  return mkAnd(expIsTop, sigIsNotZero);
}

SMTExprRef SMTFPSolver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  // Extract the exponent
  SMTExprRef exp = extractExp(*this, Exp);

  SMTExprRef zero = mkBVFromDec(0, exp->getWidth());
  SMTExprRef zExp = mkEqual(exp, zero);
  SMTExprRef isZero = mkFPIsZero(Exp);
  SMTExprRef nIsZero = mkNot(isZero);
  return mkAnd(nIsZero, zExp);
}

SMTExprRef SMTFPSolver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  // Extract the exponent
  SMTExprRef exp = extractExp(*this, Exp);

  SMTExprRef isDenormal = mkFPIsDenormal(Exp);
  SMTExprRef isZero = mkFPIsZero(Exp);

  unsigned eWidth = exp->getWidth();
  SMTExprRef p = mkBVFromDec(power2m1(eWidth, false), eWidth);

  SMTExprRef isSpecial = mkEqual(exp, p);

  SMTExprRef orEx = mkOr(isSpecial, isDenormal);
  orEx = mkOr(isZero, orEx);
  return mkNot(orEx);
}

SMTExprRef SMTFPSolver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  // Both -0 and 0 should return true

  // Extract everything but the sign bit
  SMTExprRef ew_sw = extractExpSig(*this, Exp);

  // Then compare it with zero of the same size
  return mkEqual(ew_sw, mkBVFromDec(0, Exp->getWidth() - 1));
}

SMTExprRef SMTFPSolver::mkFPMulImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS, const RM &R) {
  assert(LHS->getWidth() == RHS->getWidth());
  assert(LHS->Sort->getFPExponentWidth() == RHS->Sort->getFPExponentWidth());

  std::size_t ebits = LHS->Sort->getFPExponentWidth();
  std::size_t sbits = LHS->Sort->getFPSignificandWidth();

  SMTExprRef nan = mkNaN(false, ebits, sbits);
  SMTExprRef nzero = mkNZero(*this, ebits, sbits);
  SMTExprRef pzero = mkPZero(*this, ebits, sbits);
  SMTExprRef ninf = mkNInf(*this, ebits, sbits);
  SMTExprRef pinf = mkPInf(*this, ebits, sbits);

  SMTExprRef x_is_nan = mkFPIsNaN(LHS);
  SMTExprRef x_is_zero = mkFPIsZero(LHS);
  SMTExprRef x_is_pos = mkIsPos(*this, LHS);
  SMTExprRef y_is_nan = mkFPIsNaN(RHS);
  SMTExprRef y_is_zero = mkFPIsZero(RHS);
  SMTExprRef y_is_pos = mkIsPos(*this, RHS);

  // (x is NaN) || (y is NaN) -> NaN
  SMTExprRef c1 = mkOr(x_is_nan, y_is_nan);
  SMTExprRef v1 = nan;

  // (x is +oo) -> if (y is 0) then NaN else inf with y's sign.
  SMTExprRef c2 = mkIsPInf(*this, LHS);
  SMTExprRef y_sgn_inf = mkIte(y_is_pos, pinf, ninf);
  SMTExprRef v2 = mkIte(y_is_zero, nan, y_sgn_inf);

  // (y is +oo) -> if (x is 0) then NaN else inf with x's sign.
  SMTExprRef c3 = mkIsPInf(*this, RHS);
  SMTExprRef x_sgn_inf = mkIte(x_is_pos, pinf, ninf);
  SMTExprRef v3 = mkIte(x_is_zero, nan, x_sgn_inf);

  // (x is -oo) -> if (y is 0) then NaN else inf with -y's sign.
  SMTExprRef c4 = mkIsNInf(*this, LHS);
  SMTExprRef neg_y_sgn_inf = mkIte(y_is_pos, ninf, pinf);
  SMTExprRef v4 = mkIte(y_is_zero, nan, neg_y_sgn_inf);

  // (y is -oo) -> if (x is 0) then NaN else inf with -x's sign.
  SMTExprRef c5 = mkIsNInf(*this, RHS);
  SMTExprRef neg_x_sgn_inf = mkIte(x_is_pos, ninf, pinf);
  SMTExprRef v5 = mkIte(x_is_zero, nan, neg_x_sgn_inf);

  // (x is 0) || (y is 0) -> x but with sign = x.sign ^ y.sign
  SMTExprRef c6 = mkOr(x_is_zero, y_is_zero);
  SMTExprRef sign_xor = mkXor(x_is_pos, y_is_pos);
  SMTExprRef v6 = mkIte(sign_xor, nzero, pzero);

  // else comes the actual multiplication.
  SMTExprRef a_sgn, a_sig, a_exp, a_lz, b_sgn, b_sig, b_exp, b_lz;
  unpack(*this, LHS, a_sgn, a_sig, a_exp, a_lz, true);
  unpack(*this, RHS, b_sgn, b_sig, b_exp, b_lz, true);

  SMTExprRef a_lz_ext = mkBVZeroExt(2, a_lz);
  SMTExprRef b_lz_ext = mkBVZeroExt(2, b_lz);

  SMTExprRef a_sig_ext = mkBVZeroExt(sbits, a_sig);
  SMTExprRef b_sig_ext = mkBVZeroExt(sbits, b_sig);

  SMTExprRef a_exp_ext = mkBVSignExt(2, a_exp);
  SMTExprRef b_exp_ext = mkBVSignExt(2, b_exp);

  SMTExprRef res_sgn, res_sig, res_exp;
  res_sgn = mkBVXor(a_sgn, b_sgn);

  res_exp = mkBVAdd(mkBVSub(a_exp_ext, a_lz_ext), mkBVSub(b_exp_ext, b_lz_ext));

  SMTExprRef product = mkBVMul(a_sig_ext, b_sig_ext);

  assert(product->getWidth() == 2 * sbits);

  SMTExprRef h_p = mkBVExtract(2 * sbits - 1, sbits, product);
  SMTExprRef l_p = mkBVExtract(sbits - 1, 0, product);

  SMTExprRef rbits;
  if (sbits >= 4) {
    SMTExprRef sticky = mkBVRedOr(mkBVExtract(sbits - 4, 0, product));
    rbits = mkBVConcat(mkBVExtract(sbits - 1, sbits - 3, product), sticky);
  } else
    rbits = mkBVConcat(l_p, mkBVFromDec(0, 4 - sbits));

  assert(rbits->getWidth() == 4);
  res_sig = mkBVConcat(h_p, rbits);

  SMTExprRef rm = mkRM(R);
  SMTExprRef v7 = round(rm, res_sgn, res_sig, res_exp, ebits, sbits);

  // And finally, we tie them together.
  SMTExprRef result = mkIte(c6, v6, v7);
  result = mkIte(c5, v5, result);
  result = mkIte(c4, v4, result);
  result = mkIte(c3, v3, result);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

SMTExprRef SMTFPSolver::mkFPDivImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS, const RM &R) {
  assert(LHS->getWidth() == RHS->getWidth());
  assert(LHS->Sort->getFPExponentWidth() == RHS->Sort->getFPExponentWidth());

  unsigned ebits = LHS->Sort->getFPExponentWidth();
  unsigned sbits = LHS->Sort->getFPSignificandWidth();

  SMTExprRef nan = mkNaN(false, ebits, sbits);
  SMTExprRef nzero = mkNZero(*this, ebits, sbits);
  SMTExprRef pzero = mkPZero(*this, ebits, sbits);
  SMTExprRef ninf = mkNInf(*this, ebits, sbits);
  SMTExprRef pinf = mkPInf(*this, ebits, sbits);

  SMTExprRef x_is_nan = mkFPIsNaN(LHS);
  SMTExprRef x_is_zero = mkFPIsZero(LHS);
  SMTExprRef x_is_pos = mkIsPos(*this, LHS);
  SMTExprRef x_is_inf = mkFPIsInfinite(LHS);
  SMTExprRef y_is_nan = mkFPIsNaN(RHS);
  SMTExprRef y_is_zero = mkFPIsZero(RHS);
  SMTExprRef y_is_pos = mkIsPos(*this, RHS);
  SMTExprRef y_is_inf = mkFPIsInfinite(RHS);

  // (x is NaN) || (y is NaN) -> NaN
  SMTExprRef c1 = mkOr(x_is_nan, y_is_nan);
  SMTExprRef v1 = nan;

  // (x is +oo) -> if (y is oo) then NaN else inf with y's sign.
  SMTExprRef c2 = mkIsPInf(*this, LHS);
  SMTExprRef y_sgn_inf = mkIte(y_is_pos, pinf, ninf);
  SMTExprRef v2 = mkIte(y_is_inf, nan, y_sgn_inf);

  // (y is +oo) -> if (x is oo) then NaN else 0 with sign x.sgn ^ y.sgn
  SMTExprRef c3 = mkIsPInf(*this, RHS);
  SMTExprRef signs_xor = mkXor(x_is_pos, y_is_pos);
  SMTExprRef xy_zero = mkIte(signs_xor, nzero, pzero);
  SMTExprRef v3 = mkIte(x_is_inf, nan, xy_zero);

  // (x is -oo) -> if (y is oo) then NaN else inf with -y's sign.
  SMTExprRef c4 = mkIsNInf(*this, LHS);
  SMTExprRef neg_y_sgn_inf = mkIte(y_is_pos, ninf, pinf);
  SMTExprRef v4 = mkIte(y_is_inf, nan, neg_y_sgn_inf);

  // (y is -oo) -> if (x is oo) then NaN else 0 with sign x.sgn ^ y.sgn
  SMTExprRef c5 = mkIsNInf(*this, RHS);
  SMTExprRef v5 = mkIte(x_is_inf, nan, xy_zero);

  // (y is 0) -> if (x is 0) then NaN else inf with xor sign.
  SMTExprRef c6 = y_is_zero;
  SMTExprRef sgn_inf = mkIte(signs_xor, ninf, pinf);
  SMTExprRef v6 = mkIte(x_is_zero, nan, sgn_inf);

  // (x is 0) -> result is zero with sgn = x.sgn^y.sgn
  // This is a special case to avoid problems with the unpacking of zero.
  SMTExprRef c7 = x_is_zero;
  SMTExprRef v7 = mkIte(signs_xor, nzero, pzero);

  // else comes the actual division.
  assert(ebits <= sbits);

  SMTExprRef a_sgn, a_sig, a_exp, a_lz, b_sgn, b_sig, b_exp, b_lz;
  unpack(*this, LHS, a_sgn, a_sig, a_exp, a_lz, true);
  unpack(*this, RHS, b_sgn, b_sig, b_exp, b_lz, true);

  unsigned extra_bits = sbits + 2;
  SMTExprRef a_sig_ext = mkBVConcat(a_sig, mkBVFromDec(0, sbits + extra_bits));
  SMTExprRef b_sig_ext = mkBVZeroExt(sbits + extra_bits, b_sig);

  SMTExprRef a_exp_ext = mkBVSignExt(2, a_exp);
  SMTExprRef b_exp_ext = mkBVSignExt(2, b_exp);

  SMTExprRef res_sgn = mkBVXor(a_sgn, b_sgn);

  SMTExprRef a_lz_ext = mkBVZeroExt(2, a_lz);
  SMTExprRef b_lz_ext = mkBVZeroExt(2, b_lz);

  SMTExprRef res_exp =
      mkBVSub(mkBVSub(a_exp_ext, a_lz_ext), mkBVSub(b_exp_ext, b_lz_ext));

  // b_sig_ext can't be 0 here, so it's safe to use OP_BUDIV_I
  SMTExprRef quotient = mkBVUDiv(a_sig_ext, b_sig_ext);

  assert(quotient->getWidth() == (sbits + sbits + extra_bits));

  SMTExprRef sticky = mkBVRedOr(mkBVExtract(extra_bits - 2, 0, quotient));
  SMTExprRef res_sig = mkBVConcat(
      mkBVExtract(extra_bits + sbits + 1, extra_bits - 1, quotient), sticky);

  assert(res_sig->getWidth() == (sbits + 4));

  SMTExprRef res_sig_lz = mkLeadingZeros(*this, res_sig, sbits + 4);
  SMTExprRef res_sig_shift_amount =
      mkBVSub(res_sig_lz, mkBVFromDec(1, sbits + 4));
  SMTExprRef shift_cond = mkBVUle(res_sig_lz, mkBVFromDec(1, sbits + 4));
  SMTExprRef res_sig_shifted = mkBVShl(res_sig, res_sig_shift_amount);
  SMTExprRef res_exp_shifted =
      mkBVSub(res_exp, mkBVExtract(ebits + 1, 0, res_sig_shift_amount));
  res_sig = mkIte(shift_cond, res_sig, res_sig_shifted);
  res_exp = mkIte(shift_cond, res_exp, res_exp_shifted);

  SMTExprRef rm = mkRM(R);
  SMTExprRef v8 = round(rm, res_sgn, res_sig, res_exp, ebits, sbits);

  // And finally, we tie them together.
  SMTExprRef result = mkIte(c7, v7, v8);
  result = mkIte(c6, v6, result);
  result = mkIte(c5, v5, result);
  result = mkIte(c4, v4, result);
  result = mkIte(c3, v3, result);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

SMTExprRef SMTFPSolver::mkFPRemImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return mkBVSub(LHS, mkBVMul(mkBVSDiv(LHS, RHS), RHS));
}

static inline void addCore(SMTSolver &S, unsigned int SWidth,
                           unsigned int EWidth, SMTExprRef &CSgn,
                           SMTExprRef &CSig, SMTExprRef &CExp, SMTExprRef &DSgn,
                           SMTExprRef &DSig, SMTExprRef &DExp,
                           SMTExprRef &ResSgn, SMTExprRef &ResSig,
                           SMTExprRef &ResExp) {
  // c/d are now such that c_exp >= d_exp.
  SMTExprRef exp_delta = S.mkBVSub(CExp, DExp);

  if (log2(SWidth + 2) < EWidth + 2) {
    // cap the delta
    SMTExprRef cap = S.mkBVFromDec(SWidth + 2, EWidth + 2);
    SMTExprRef cap_le_delta = S.mkBVUle(cap, S.mkBVZeroExt(2, exp_delta));
    SMTExprRef exp_delta_ext = S.mkBVZeroExt(2, exp_delta);
    exp_delta = S.mkIte(cap_le_delta, cap, exp_delta_ext);
    exp_delta = S.mkBVExtract(EWidth - 1, 0, exp_delta);
  }

  // Three extra bits for c/d
  CSig = S.mkBVConcat(CSig, S.mkBVFromDec(0, 3));
  DSig = S.mkBVConcat(DSig, S.mkBVFromDec(0, 3));

  // Alignment shift with sticky bit computation.
  SMTExprRef big_d_sig = S.mkBVConcat(S.mkBVFromDec(0, SWidth + 3), DSig);

  SMTExprRef shifted_big = S.mkBVLshr(
      big_d_sig,
      S.mkBVConcat(S.mkBVFromDec(0, (2 * (SWidth + 3)) - EWidth), exp_delta));
  SMTExprRef shifted_d_sig =
      S.mkBVExtract((2 * (SWidth + 3) - 1), (SWidth + 3), shifted_big);

  SMTExprRef sticky_raw = S.mkBVExtract(SWidth + 2, 0, shifted_big);
  SMTExprRef nil_sbit3 = S.mkBVFromDec(0, SWidth + 3);
  SMTExprRef one_sbit3 = S.mkBVFromDec(1, SWidth + 3);
  SMTExprRef sticky_eq = S.mkEqual(sticky_raw, nil_sbit3);
  SMTExprRef sticky = S.mkIte(sticky_eq, nil_sbit3, one_sbit3);

  shifted_d_sig = S.mkBVOr(shifted_d_sig, sticky);

  SMTExprRef eq_sgn = S.mkEqual(CSgn, DSgn);

  // two extra bits for catching the overflow.
  CSig = S.mkBVZeroExt(2, CSig);
  shifted_d_sig = S.mkBVZeroExt(2, shifted_d_sig);

  assert(CSig->getWidth() == SWidth + 5);
  assert(shifted_d_sig->getWidth() == SWidth + 5);

  SMTExprRef c_plus_d = S.mkBVAdd(shifted_d_sig, CSig);
  SMTExprRef c_minus_d = S.mkBVSub(shifted_d_sig, CSig);
  SMTExprRef sum = S.mkIte(eq_sgn, c_plus_d, c_minus_d);

  SMTExprRef sign_bv = S.mkBVExtract(SWidth + 4, SWidth + 4, sum);
  SMTExprRef n_sum = S.mkBVNeg(sum);

  SMTExprRef not_c_sgn = S.mkBVNot(CSgn);
  SMTExprRef not_d_sgn = S.mkBVNot(DSgn);
  SMTExprRef not_sign_bv = S.mkBVNot(sign_bv);
  SMTExprRef res_sgn_c1 = S.mkBVAnd(S.mkBVAnd(not_c_sgn, DSgn), sign_bv);
  SMTExprRef res_sgn_c2 = S.mkBVAnd(S.mkBVAnd(CSgn, not_d_sgn), not_sign_bv);
  SMTExprRef res_sgn_c3 = S.mkBVAnd(CSgn, DSgn);
  ResSgn = S.mkBVOr(S.mkBVOr(res_sgn_c1, res_sgn_c2), res_sgn_c3);

  SMTExprRef one_1 = S.mkBVFromDec(1, 1);
  SMTExprRef res_sig_eq = S.mkEqual(sign_bv, one_1);
  SMTExprRef sig_abs = S.mkIte(res_sig_eq, n_sum, sum);

  ResSig = S.mkBVExtract(SWidth + 3, 0, sig_abs);
  ResExp = S.mkBVSignExt(2, CExp); // rounder requires 2 extra bits!
}

SMTExprRef SMTFPSolver::mkFPAddImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS, const RM &R) {
  assert(LHS->getWidth() == RHS->getWidth());
  assert(LHS->Sort->getFPExponentWidth() == RHS->Sort->getFPExponentWidth());

  std::size_t ebits = LHS->Sort->getFPExponentWidth();
  std::size_t sbits = LHS->Sort->getFPSignificandWidth();

  SMTExprRef nan = mkNaN(false, ebits, sbits);
  SMTExprRef nzero = mkNZero(*this, ebits, sbits);
  SMTExprRef pzero = mkPZero(*this, ebits, sbits);

  SMTExprRef x_is_nan = mkFPIsNaN(LHS);
  SMTExprRef x_is_zero = mkFPIsZero(LHS);
  SMTExprRef x_is_neg = mkIsNeg(*this, LHS);
  SMTExprRef x_is_inf = mkFPIsInfinite(LHS);
  SMTExprRef y_is_nan = mkFPIsNaN(RHS);
  SMTExprRef y_is_zero = mkFPIsZero(RHS);
  SMTExprRef y_is_neg = mkIsNeg(*this, RHS);
  SMTExprRef y_is_inf = mkFPIsInfinite(RHS);

  SMTExprRef c1 = mkOr(x_is_nan, y_is_nan);
  SMTExprRef v1 = nan;

  SMTExprRef c2 = mkFPIsInfinite(LHS);
  SMTExprRef nx = mkIsNeg(*this, LHS);
  SMTExprRef ny = mkIsNeg(*this, RHS);
  SMTExprRef nx_xor_ny = mkXor(nx, ny);
  SMTExprRef inf_xor = mkAnd(y_is_inf, nx_xor_ny);
  SMTExprRef v2 = mkIte(inf_xor, nan, LHS);

  SMTExprRef c3 = mkFPIsInfinite(RHS);
  SMTExprRef xy_is_neg = mkXor(x_is_neg, y_is_neg);
  SMTExprRef v3_and = mkAnd(x_is_inf, xy_is_neg);
  SMTExprRef v3 = mkIte(v3_and, nan, RHS);

  SMTExprRef c4 = mkAnd(x_is_zero, y_is_zero);
  SMTExprRef signs_and = mkAnd(x_is_neg, y_is_neg);
  SMTExprRef signs_xor = mkXor(x_is_neg, y_is_neg);
  SMTExprRef rm = mkRM(R);
  SMTExprRef rm_is_to_neg = mkIsRM(*this, rm, RM::ROUND_TO_MINUS_INF);
  SMTExprRef rm_and_xor = mkAnd(rm_is_to_neg, signs_xor);
  SMTExprRef neg_cond = mkOr(signs_and, rm_and_xor);
  SMTExprRef v4 = mkIte(neg_cond, nzero, pzero);
  SMTExprRef v4_and = mkAnd(x_is_neg, y_is_neg);
  v4 = mkIte(v4_and, LHS, v4);

  SMTExprRef c5 = x_is_zero;
  SMTExprRef v5 = RHS;

  SMTExprRef c6 = y_is_zero;
  SMTExprRef v6 = LHS;

  // Actual addition.
  SMTExprRef a_sgn, a_sig, a_exp, a_lz, b_sgn, b_sig, b_exp, b_lz;
  unpack(*this, LHS, a_sgn, a_sig, a_exp, a_lz, false);
  unpack(*this, RHS, b_sgn, b_sig, b_exp, b_lz, false);

  SMTExprRef swap_cond = mkBVSle(a_exp, b_exp);

  SMTExprRef c_sgn = mkIte(swap_cond, b_sgn, a_sgn);
  SMTExprRef c_sig = mkIte(swap_cond, b_sig, a_sig); // has sbits
  SMTExprRef c_exp = mkIte(swap_cond, b_exp, a_exp); // has ebits
  SMTExprRef d_sgn = mkIte(swap_cond, a_sgn, b_sgn);
  SMTExprRef d_sig = mkIte(swap_cond, a_sig, b_sig); // has sbits
  SMTExprRef d_exp = mkIte(swap_cond, a_exp, b_exp); // has ebits

  SMTExprRef res_sgn, res_sig, res_exp;
  addCore(*this, sbits, ebits, c_sgn, c_sig, c_exp, d_sgn, d_sig, d_exp,
          res_sgn, res_sig, res_exp);

  SMTExprRef nil_sbit4 = mkBVFromDec(0, sbits + 4);
  SMTExprRef is_zero_sig = mkEqual(res_sig, nil_sbit4);

  SMTExprRef zero_case = mkIte(rm_is_to_neg, nzero, pzero);

  SMTExprRef rounded = round(rm, res_sgn, res_sig, res_exp, ebits, sbits);

  SMTExprRef v7 = mkIte(is_zero_sig, zero_case, rounded);

  SMTExprRef result = mkIte(c6, v6, v7);
  result = mkIte(c5, v5, result);
  result = mkIte(c4, v4, result);
  result = mkIte(c3, v3, result);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

SMTExprRef SMTFPSolver::mkFPSubImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS, const RM &R) {
  return mkFPAdd(LHS, mkFPNeg(RHS), R);
}

SMTExprRef SMTFPSolver::mkFPSqrtImpl(const SMTExprRef &Exp, const RM &RM) {
  unsigned ebits = Exp->Sort->getFPExponentWidth();
  unsigned sbits = Exp->Sort->getFPSignificandWidth();

  SMTExprRef nan = mkNaN(false, ebits, sbits);

  SMTExprRef x_is_nan = mkFPIsNaN(Exp);

  SMTExprRef zero1 = mkBVFromDec(0, 1);
  SMTExprRef one1 = mkBVFromDec(1, 1);

  // (x is NaN) -> NaN
  SMTExprRef c1 = x_is_nan;
  SMTExprRef v1 = Exp;

  // (x is +oo) -> +oo
  SMTExprRef c2 = mkIsPInf(*this, Exp);
  SMTExprRef v2 = Exp;

  // (x is +-0) -> +-0
  SMTExprRef c3 = mkFPIsZero(Exp);
  SMTExprRef v3 = Exp;

  // (x < 0) -> NaN
  SMTExprRef c4 = mkIsNeg(*this, Exp);
  SMTExprRef v4 = nan;

  // else comes the actual square root.

  SMTExprRef a_sgn, a_sig, a_exp, a_lz;
  unpack(*this, Exp, a_sgn, a_sig, a_exp, a_lz, true);

  assert(a_sig->getWidth() == sbits);
  assert(a_exp->getWidth() == ebits);

  SMTExprRef res_sgn = zero1;

  SMTExprRef real_exp = mkBVSub(mkBVSignExt(1, a_exp), mkBVZeroExt(1, a_lz));
  SMTExprRef res_exp = mkBVSignExt(2, mkBVExtract(ebits, 1, real_exp));

  SMTExprRef e_is_odd = mkEqual(mkBVExtract(0, 0, real_exp), one1);

  SMTExprRef a_z = mkBVConcat(a_sig, zero1);
  SMTExprRef z_a = mkBVConcat(zero1, a_sig);
  SMTExprRef sig_prime = mkIte(e_is_odd, a_z, z_a);
  assert(sig_prime->getWidth() == sbits + 1);

  // This is algorithm 10.2 in the Handbook of Floating-Point Arithmetic
  auto p2 = power2(sbits + 3, false);
  SMTExprRef Q = mkBVFromDec(p2, sbits + 5);
  SMTExprRef R = mkBVSub(mkBVConcat(sig_prime, mkBVFromDec(0, 4)), Q);
  SMTExprRef S = Q;

  SMTExprRef T;
  for (unsigned i = 0; i < sbits + 3; i++) {
    S = mkBVConcat(zero1, mkBVExtract(sbits + 4, 1, S));

    SMTExprRef twoQ_plus_S =
        mkBVAdd(mkBVConcat(Q, zero1), mkBVConcat(zero1, S));
    T = mkBVSub(mkBVConcat(R, zero1), twoQ_plus_S);

    assert(Q->getWidth() == sbits + 5);
    assert(R->getWidth() == sbits + 5);
    assert(S->getWidth() == sbits + 5);
    assert(T->getWidth() == sbits + 6);

    SMTExprRef T_lsds5 = mkBVExtract(sbits + 5, sbits + 5, T);
    SMTExprRef t_lt_0 = mkEqual(T_lsds5, one1);

    SMTExprRef Q_or_S = mkBVOr(Q, S);
    Q = mkIte(t_lt_0, Q, Q_or_S);
    SMTExprRef R_shftd = mkBVConcat(mkBVExtract(sbits + 3, 0, R), zero1);
    SMTExprRef T_lsds4 = mkBVExtract(sbits + 4, 0, T);
    R = mkIte(t_lt_0, R_shftd, T_lsds4);
  }

  SMTExprRef zero_sbits5 = mkBVFromDec(0, sbits + 5);
  SMTExprRef is_exact = mkEqual(R, zero_sbits5);

  SMTExprRef last = mkBVExtract(0, 0, Q);
  SMTExprRef rest = mkBVExtract(sbits + 3, 1, Q);
  SMTExprRef rest_ext = mkBVZeroExt(1, rest);
  SMTExprRef last_ext = mkBVZeroExt(sbits + 3, last);
  SMTExprRef one_sbits4 = mkBVFromDec(1, sbits + 4);
  SMTExprRef sticky = mkIte(is_exact, last_ext, one_sbits4);
  SMTExprRef res_sig = mkBVOr(rest_ext, sticky);

  assert(res_sig->getWidth() == sbits + 4);

  SMTExprRef rm = mkRM(RM);
  SMTExprRef v5 = round(rm, res_sgn, res_sig, res_exp, ebits, sbits);

  // And finally, we tie them together.
  SMTExprRef result = mkIte(c4, v4, v5);
  result = mkIte(c3, v3, result);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

SMTExprRef SMTFPSolver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                    const SMTExprRef &Z, const RM &R) {
  assert(X->getWidth() == Y->getWidth());
  assert(X->Sort->getFPExponentWidth() == Y->Sort->getFPExponentWidth());
  assert(X->getWidth() == Y->getWidth());
  assert(X->Sort->getFPExponentWidth() == Y->Sort->getFPExponentWidth());

  unsigned ebits = X->Sort->getFPExponentWidth();
  unsigned sbits = X->Sort->getFPSignificandWidth();

  SMTExprRef nan = mkNaN(false, ebits, sbits);
  SMTExprRef nzero = mkNZero(*this, ebits, sbits);
  SMTExprRef pzero = mkPZero(*this, ebits, sbits);
  SMTExprRef ninf = mkNInf(*this, ebits, sbits);
  SMTExprRef pinf = mkPInf(*this, ebits, sbits);

  SMTExprRef x_is_nan = mkFPIsNaN(X);
  SMTExprRef x_is_zero = mkFPIsZero(X);
  SMTExprRef x_is_pos = mkIsPos(*this, X);
  SMTExprRef x_is_neg = mkIsNeg(*this, X);
  SMTExprRef y_is_nan = mkFPIsNaN(Y);
  SMTExprRef y_is_zero = mkFPIsZero(Y);
  SMTExprRef y_is_pos = mkIsPos(*this, Y);
  SMTExprRef y_is_neg = mkIsNeg(*this, Y);
  SMTExprRef z_is_nan = mkFPIsNaN(Z);
  SMTExprRef z_is_zero = mkFPIsZero(Z);
  SMTExprRef z_is_neg = mkIsNeg(*this, Z);
  SMTExprRef z_is_inf = mkFPIsInfinite(Z);

  SMTExprRef rm = mkRM(R);
  SMTExprRef rm_is_to_neg = mkIsRM(*this, rm, RM::ROUND_TO_MINUS_INF);

  SMTExprRef inf_xor = mkXor(x_is_neg, y_is_neg);
  inf_xor = mkXor(inf_xor, z_is_neg);
  SMTExprRef inf_cond = mkAnd(z_is_inf, inf_xor);

  // (x is NaN) || (y is NaN) || (z is Nan) -> NaN
  SMTExprRef c1 = mkOr(mkOr(x_is_nan, y_is_nan), z_is_nan);
  SMTExprRef v1 = nan;

  // (x is +oo) -> if (y is 0) then NaN else inf with y's sign.
  SMTExprRef c2 = mkIsPInf(*this, X);
  SMTExprRef y_sgn_inf = mkIte(y_is_pos, pinf, ninf);
  SMTExprRef inf_or = mkOr(y_is_zero, inf_cond);
  SMTExprRef v2 = mkIte(inf_or, nan, y_sgn_inf);

  // (y is +oo) -> if (x is 0) then NaN else inf with x's sign.
  SMTExprRef c3 = mkIsPInf(*this, Y);
  SMTExprRef x_sgn_inf = mkIte(x_is_pos, pinf, ninf);
  inf_or = mkOr(x_is_zero, inf_cond);
  SMTExprRef v3 = mkIte(inf_or, nan, x_sgn_inf);

  // (x is -oo) -> if (y is 0) then NaN else inf with -y's sign.
  SMTExprRef c4 = mkIsNInf(*this, X);
  SMTExprRef neg_y_sgn_inf = mkIte(y_is_pos, ninf, pinf);
  inf_or = mkOr(y_is_zero, inf_cond);
  SMTExprRef v4 = mkIte(inf_or, nan, neg_y_sgn_inf);

  // (y is -oo) -> if (x is 0) then NaN else inf with -x's sign.
  SMTExprRef c5 = mkIsNInf(*this, Y);
  SMTExprRef neg_x_sgn_inf = mkIte(x_is_pos, ninf, pinf);
  inf_or = mkOr(x_is_zero, inf_cond);
  SMTExprRef v5 = mkIte(inf_or, nan, neg_x_sgn_inf);

  // z is +-INF -> z.
  SMTExprRef c6 = mkFPIsInfinite(Z);
  SMTExprRef v6 = Z;

  // (x is 0) || (y is 0) -> z
  SMTExprRef c7 = mkOr(x_is_zero, y_is_zero);
  SMTExprRef xy_sgn = mkXor(x_is_neg, y_is_neg);

  SMTExprRef xyz_sgn = mkXor(xy_sgn, z_is_neg);
  SMTExprRef c71 = mkAnd(z_is_zero, xyz_sgn);

  SMTExprRef zero_cond = mkIte(rm_is_to_neg, nzero, pzero);
  SMTExprRef v7 = mkIte(c71, zero_cond, Z);

  // else comes the fused multiplication.
  SMTExprRef one_1 = mkBVFromDec(1, 1);
  SMTExprRef zero_1 = mkBVFromDec(0, 1);

  SMTExprRef a_sgn, a_sig, a_exp, a_lz;
  SMTExprRef b_sgn, b_sig, b_exp, b_lz;
  SMTExprRef c_sgn, c_sig, c_exp, c_lz;
  unpack(*this, X, a_sgn, a_sig, a_exp, a_lz, true);
  unpack(*this, Y, b_sgn, b_sig, b_exp, b_lz, true);
  unpack(*this, Z, c_sgn, c_sig, c_exp, c_lz, true);

  SMTExprRef a_lz_ext = mkBVZeroExt(2, a_lz);
  SMTExprRef b_lz_ext = mkBVZeroExt(2, b_lz);
  SMTExprRef c_lz_ext = mkBVZeroExt(2, c_lz);

  SMTExprRef a_sig_ext = mkBVZeroExt(sbits, a_sig);
  SMTExprRef b_sig_ext = mkBVZeroExt(sbits, b_sig);

  SMTExprRef a_exp_ext = mkBVSignExt(2, a_exp);
  SMTExprRef b_exp_ext = mkBVSignExt(2, b_exp);
  SMTExprRef c_exp_ext = mkBVSignExt(2, c_exp);

  SMTExprRef mul_sgn = mkBVXor(a_sgn, b_sgn);

  SMTExprRef mul_exp =
      mkBVAdd(mkBVSub(a_exp_ext, a_lz_ext), mkBVSub(b_exp_ext, b_lz_ext));

  SMTExprRef mul_sig = mkBVMul(a_sig_ext, b_sig_ext);

  assert(mul_sig->getWidth() == 2 * sbits);
  assert(mul_exp->getWidth() == ebits + 2);

  // The product has the form [-1][0].[2*sbits - 2].

  // Extend c
  SMTExprRef c_sig_ext =
      mkBVZeroExt(1, mkBVConcat(c_sig, mkBVFromDec(0, sbits + 2)));
  c_exp_ext = mkBVSub(c_exp_ext, c_lz_ext);
  mul_sig = mkBVConcat(mul_sig, mkBVFromDec(0, 3));

  assert(mul_sig->getWidth() == 2 * sbits + 3);
  assert(c_sig_ext->getWidth() == 2 * sbits + 3);

  SMTExprRef swap_cond = mkBVSle(mul_exp, c_exp_ext);

  SMTExprRef e_sgn = mkIte(swap_cond, c_sgn, mul_sgn);
  SMTExprRef e_sig = mkIte(swap_cond, c_sig_ext, mul_sig); // has 2 * sbits + 3
  SMTExprRef e_exp = mkIte(swap_cond, c_exp_ext, mul_exp); // has ebits + 2
  SMTExprRef f_sgn = mkIte(swap_cond, mul_sgn, c_sgn);
  SMTExprRef f_sig = mkIte(swap_cond, mul_sig, c_sig_ext); // has 2 * sbits + 3
  SMTExprRef f_exp = mkIte(swap_cond, mul_exp, c_exp_ext); // has ebits + 2

  assert(e_sig->getWidth() == 2 * sbits + 3);
  assert(f_sig->getWidth() == 2 * sbits + 3);
  assert(e_exp->getWidth() == ebits + 2);
  assert(f_exp->getWidth() == ebits + 2);

  SMTExprRef exp_delta = mkBVSub(e_exp, f_exp);

  // cap the delta

  SMTExprRef cap = mkBVFromDec(2 * sbits + 3, ebits + 2);
  SMTExprRef cap_le_delta = mkBVUle(cap, exp_delta);
  exp_delta = mkIte(cap_le_delta, cap, exp_delta);
  assert(exp_delta->getWidth() == ebits + 2);

  // Alignment shift with sticky bit computation.
  SMTExprRef shifted_big =
      mkBVLshr(mkBVConcat(f_sig, mkBVFromDec(0, sbits)),
               mkBVZeroExt((3 * sbits + 3) - (ebits + 2), exp_delta));
  SMTExprRef shifted_f_sig = mkBVExtract(3 * sbits + 2, sbits, shifted_big);
  SMTExprRef alignment_sticky_raw = mkBVExtract(sbits - 1, 0, shifted_big);
  SMTExprRef alignment_sticky = mkBVRedOr(alignment_sticky_raw);
  assert(shifted_f_sig->getWidth() == 2 * sbits + 3);

  // Significant addition.
  // Two extra bits for the sign and for catching overflows.
  e_sig = mkBVZeroExt(2, e_sig);
  shifted_f_sig = mkBVZeroExt(2, shifted_f_sig);

  SMTExprRef eq_sgn = mkEqual(e_sgn, f_sgn);

  assert(e_sig->getWidth() == 2 * sbits + 5);
  assert(shifted_f_sig->getWidth() == 2 * sbits + 5);

  SMTExprRef sticky_wide = mkBVZeroExt(2 * sbits + 4, alignment_sticky);
  SMTExprRef e_plus_f = mkBVAdd(e_sig, shifted_f_sig);
  e_plus_f = mkIte(mkEqual(mkBVExtract(0, 0, e_plus_f), zero_1),
                   mkBVAdd(e_plus_f, sticky_wide), e_plus_f);
  SMTExprRef e_minus_f = mkBVSub(e_sig, shifted_f_sig);
  e_minus_f = mkIte(mkEqual(mkBVExtract(0, 0, e_minus_f), zero_1),
                    mkBVSub(e_minus_f, sticky_wide), e_minus_f);

  SMTExprRef sum = mkIte(eq_sgn, e_plus_f, e_minus_f);
  assert(sum->getWidth() == 2 * sbits + 5);

  SMTExprRef sign_bv = mkBVExtract(2 * sbits + 4, 2 * sbits + 4, sum);
  SMTExprRef n_sum = mkBVNeg(sum);

  SMTExprRef res_sig_eq = mkEqual(sign_bv, one_1);
  SMTExprRef sig_abs = mkIte(res_sig_eq, n_sum, sum);

  SMTExprRef not_e_sgn = mkBVNot(e_sgn);
  SMTExprRef not_f_sgn = mkBVNot(f_sgn);
  SMTExprRef not_sign_bv = mkBVNot(sign_bv);

  SMTExprRef res_sgn_c1 = mkBVAnd(mkBVAnd(not_e_sgn, f_sgn), sign_bv);
  SMTExprRef res_sgn_c2 = mkBVAnd(mkBVAnd(e_sgn, not_f_sgn), not_sign_bv);
  SMTExprRef res_sgn_c3 = mkBVAnd(e_sgn, f_sgn);
  SMTExprRef res_sgn = mkBVOr(mkBVOr(res_sgn_c1, res_sgn_c2), res_sgn_c3);

  SMTExprRef is_sig_neg =
      mkEqual(one_1, mkBVExtract(2 * sbits + 4, 2 * sbits + 4, sig_abs));
  sig_abs = mkIte(is_sig_neg, mkBVNeg(sig_abs), sig_abs);

  // Result could have overflown into 4.xxx.
  assert(sig_abs->getWidth() == 2 * sbits + 5);
  SMTExprRef extra = mkBVExtract(2 * sbits + 4, 2 * sbits + 3, sig_abs);
  SMTExprRef extra_is_zero = mkEqual(extra, mkBVFromDec(0, 2));

  SMTExprRef res_exp =
      mkIte(extra_is_zero, e_exp, mkBVAdd(e_exp, mkBVFromDec(1, ebits + 2)));

  // Renormalize
  SMTExprRef zero_e2 = mkBVFromDec(0, ebits + 2);
  SMTExprRef min_exp = mkMinExp(*this, ebits);
  min_exp = mkBVSignExt(2, min_exp);
  SMTExprRef sig_lz = mkLeadingZeros(*this, sig_abs, ebits + 2);
  sig_lz = mkBVSub(sig_lz, mkBVFromDec(2, ebits + 2));
  SMTExprRef max_exp_delta = mkBVSub(res_exp, min_exp);
  SMTExprRef sig_lz_capped =
      mkIte(mkBVSle(sig_lz, max_exp_delta), sig_lz, max_exp_delta);
  SMTExprRef renorm_delta =
      mkIte(mkBVSle(zero_e2, sig_lz_capped), sig_lz_capped, zero_e2);
  res_exp = mkBVSub(res_exp, renorm_delta);
  sig_abs = mkBVShl(sig_abs, mkBVZeroExt(2 * sbits + 3 - ebits, renorm_delta));

  unsigned too_short = 0;
  if (sbits < 5) {
    too_short = 6 - sbits + 1;
    sig_abs = mkBVConcat(sig_abs, mkBVFromDec(0, too_short));
  }

  SMTExprRef sticky_h1 = mkBVExtract(sbits + too_short - 2, 0, sig_abs);
  SMTExprRef sig_abs_h1 =
      mkBVExtract(2 * sbits + too_short + 4, sbits - 1 + too_short, sig_abs);
  SMTExprRef sticky_h1_red = mkBVZeroExt(sbits + 5, mkBVRedOr(sticky_h1));
  SMTExprRef sig_abs_h1_f = mkBVOr(sig_abs_h1, sticky_h1_red);
  SMTExprRef res_sig_1 = mkBVExtract(sbits + 3, 0, sig_abs_h1_f);
  assert(sticky_h1->getWidth() == sbits + too_short - 1);
  assert(sig_abs_h1->getWidth() == sbits + 6);
  assert(sticky_h1_red->getWidth() == sbits + 6);
  assert(sig_abs_h1_f->getWidth() == sbits + 6);
  assert(res_sig_1->getWidth() == sbits + 4);

  SMTExprRef sig_abs_h2 =
      mkBVExtract(2 * sbits + too_short + 4, sbits + too_short, sig_abs);
  SMTExprRef sticky_h2_red = mkBVZeroExt(sbits + 4, mkBVRedOr(sticky_h1));
  SMTExprRef sig_abs_h2_f = mkBVZeroExt(1, mkBVOr(sig_abs_h2, sticky_h2_red));
  SMTExprRef res_sig_2 = mkBVExtract(sbits + 3, 0, sig_abs_h2_f);
  assert(sig_abs_h2->getWidth() == sbits + 5);
  assert(sticky_h2_red->getWidth() == sbits + 5);
  assert(sig_abs_h2_f->getWidth() == sbits + 6);
  assert(res_sig_2->getWidth() == sbits + 4);

  SMTExprRef res_sig = mkIte(extra_is_zero, res_sig_1, res_sig_2);

  assert(res_sig->getWidth() == sbits + 4);

  SMTExprRef nil_sbits4 = mkBVFromDec(0, sbits + 4);
  SMTExprRef is_zero_sig = mkEqual(res_sig, nil_sbits4);

  SMTExprRef zero_case = mkIte(rm_is_to_neg, nzero, pzero);

  SMTExprRef rounded = round(rm, res_sgn, res_sig, res_exp, ebits, sbits);

  SMTExprRef v8 = mkIte(is_zero_sig, zero_case, rounded);

  // And finally, we tie them together.
  SMTExprRef result = mkIte(c7, v7, v8);
  result = mkIte(c6, v6, result);
  result = mkIte(c5, v5, result);
  result = mkIte(c4, v4, result);
  result = mkIte(c3, v3, result);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

SMTExprRef SMTFPSolver::mkFPLtImpl(const SMTExprRef &LHS,
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

  SMTExprRef one_1 = mkBVFromDec(1, 1);
  SMTExprRef nil_1 = mkBVFromDec(0, 1);
  SMTExprRef c3 = mkEqual(x_sgn, one_1);

  SMTExprRef y_sgn_eq_0 = mkEqual(y_sgn, nil_1);
  SMTExprRef y_lt_x_exp = mkBVUlt(y_exp, x_exp);
  SMTExprRef y_lt_x_sig = mkBVUlt(y_sig, x_sig);
  SMTExprRef y_eq_x_exp = mkEqual(y_exp, x_exp);
  SMTExprRef y_le_x_sig_exp = mkAnd(y_eq_x_exp, y_lt_x_sig);
  SMTExprRef t3_or = mkOr(y_lt_x_exp, y_le_x_sig_exp);
  SMTExprRef t3 = mkIte(y_sgn_eq_0, mkBool(true), t3_or);

  SMTExprRef y_sgn_eq_1 = mkEqual(y_sgn, one_1);
  SMTExprRef x_lt_y_exp = mkBVUlt(x_exp, y_exp);
  SMTExprRef x_eq_y_exp = mkEqual(x_exp, y_exp);
  SMTExprRef x_lt_y_sig = mkBVUlt(x_sig, y_sig);
  SMTExprRef x_le_y_sig_exp = mkAnd(x_eq_y_exp, x_lt_y_sig);
  SMTExprRef t4_or = mkOr(x_lt_y_exp, x_le_y_sig_exp);
  SMTExprRef t4 = mkIte(y_sgn_eq_1, mkBool(false), t4_or);

  SMTExprRef c3t3t4 = mkIte(c3, t3, t4);
  SMTExprRef c2else = mkIte(c2, mkBool(false), c3t3t4);
  return mkIte(c1, mkBool(false), c2else);
}

SMTExprRef SMTFPSolver::mkFPLeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  SMTExprRef lt = mkFPLt(LHS, RHS);
  SMTExprRef eq = mkFPEqual(LHS, RHS);
  return mkOr(lt, eq);
}

SMTExprRef SMTFPSolver::mkFPEqualImpl(const SMTExprRef &LHS,
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

SMTExprRef SMTFPSolver::mkFPtoFPImpl(const SMTExprRef &From,
                                     const SMTSortRef &To, const RM &R) {
  unsigned from_sbits = From->Sort->getFPSignificandWidth();
  unsigned from_ebits = From->Sort->getFPExponentWidth();
  unsigned to_sbits = To->getFPSignificandWidth();
  unsigned to_ebits = To->getFPExponentWidth();

  if (from_sbits == to_sbits && from_ebits == to_ebits)
    return From;

  SMTExprRef one1 = mkBVFromDec(1, 1);
  SMTExprRef pinf = mkPInf(*this, to_ebits, to_sbits);
  SMTExprRef ninf = mkNInf(*this, to_ebits, to_sbits);

  // NaN -> NaN
  SMTExprRef c1 = mkFPIsNaN(From);
  SMTExprRef v1 = mkIte(mkIsNeg(*this, From), mkNaN(true, to_ebits, to_sbits),
                        mkNaN(false, to_ebits, to_sbits));

  // +0 -> +0
  SMTExprRef c2 = mkIsPZero(*this, From);
  SMTExprRef v2 = mkPZero(*this, to_ebits, to_sbits);

  // -0 -> -0
  SMTExprRef c3 = mkIsNZero(*this, From);
  SMTExprRef v3 = mkNZero(*this, to_ebits, to_sbits);

  // +oo -> +oo
  SMTExprRef c4 = mkIsPInf(*this, From);
  SMTExprRef v4 = pinf;

  // -oo -> -oo
  SMTExprRef c5 = mkIsNInf(*this, From);
  SMTExprRef v5 = ninf;

  // otherwise: the actual conversion with rounding.
  SMTExprRef sgn, sig, exp, lz;
  unpack(*this, From, sgn, sig, exp, lz, true);

  SMTExprRef res_sgn = sgn;

  assert(sgn->getWidth() == 1);
  assert(sig->getWidth() == from_sbits);
  assert(exp->getWidth() == from_ebits);
  assert(lz->getWidth() == from_ebits);

  SMTExprRef res_sig;
  if (from_sbits < (to_sbits + 3)) {
    // make sure that sig has at least to_sbits + 3
    res_sig = mkBVConcat(sig, mkBVFromDec(0, to_sbits + 3 - from_sbits));
  } else if (from_sbits > (to_sbits + 3)) {
    // collapse the extra bits into a sticky bit.
    SMTExprRef high =
        mkBVExtract(from_sbits - 1, from_sbits - to_sbits - 2, sig);
    assert(high->getWidth() == to_sbits + 2);
    SMTExprRef low = mkBVExtract(from_sbits - to_sbits - 3, 0, sig);
    SMTExprRef sticky = mkBVRedOr(low);
    assert(sticky->getWidth() == 1);
    res_sig = mkBVConcat(high, sticky);
    assert(res_sig->getWidth() == to_sbits + 3);
  } else
    res_sig = sig;

  // extra zero in the front for the rounder.
  res_sig = mkBVZeroExt(1, res_sig);
  assert(res_sig->getWidth() == to_sbits + 4);

  SMTExprRef exponent_overflow = mkBool(false);

  SMTExprRef res_exp;
  if (from_ebits < (to_ebits + 2)) {
    res_exp = mkBVSignExt(to_ebits - from_ebits + 2, exp);

    // subtract lz for subnormal numbers.
    SMTExprRef lz_ext = mkBVZeroExt(to_ebits - from_ebits + 2, lz);
    res_exp = mkBVSub(res_exp, lz_ext);
  } else if (from_ebits > (to_ebits + 2)) {
    unsigned ebits_diff = from_ebits - (to_ebits + 2);

    // subtract lz for subnormal numbers.
    SMTExprRef exp_sub_lz = mkBVSub(mkBVSignExt(2, exp), mkBVSignExt(2, lz));

    // check whether exponent is within roundable (to_ebits+2) range.
    unsigned int z = power2(to_ebits + 1, true);
    SMTExprRef max_exp =
        mkBVConcat(mkBVFromDec(power2m1(to_ebits, false), to_ebits + 1),
                   mkBVFromDec(0, 1));
    SMTExprRef min_exp = mkBVFromDec(z + 2, to_ebits + 2);

    unsigned int ovft = power2m1(to_ebits + 1, false);
    SMTExprRef first_ovf_exp = mkBVFromDec(ovft, from_ebits + 2);
    SMTExprRef first_udf_exp = mkBVConcat(
        mkBVNeg(mkBVFromDec(1, ebits_diff + 3)), mkBVFromDec(1, to_ebits + 1));

    SMTExprRef exp_in_range = mkBVExtract(to_ebits + 1, 0, exp_sub_lz);
    assert(exp_in_range->getWidth() == to_ebits + 2);

    SMTExprRef ovf_cond = mkBVSle(first_ovf_exp, exp_sub_lz);
    SMTExprRef udf_cond = mkBVSle(exp_sub_lz, first_udf_exp);

    res_exp = exp_in_range;
    res_exp = mkIte(ovf_cond, max_exp, res_exp);
    res_exp = mkIte(udf_cond, min_exp, res_exp);
  } else {
    // from_ebits == (to_ebits + 2)
    res_exp = mkBVSub(exp, lz);
  }

  assert(res_exp->getWidth() == to_ebits + 2);

  SMTExprRef rm = mkRM(R);
  SMTExprRef rounded = round(rm, res_sgn, res_sig, res_exp, to_ebits, to_sbits);

  SMTExprRef is_neg = mkEqual(sgn, one1);
  SMTExprRef sig_inf = mkIte(is_neg, ninf, pinf);

  SMTExprRef v6 = mkIte(exponent_overflow, sig_inf, rounded);

  // And finally, we tie them together.
  SMTExprRef result = mkIte(c5, v5, v6);
  result = mkIte(c4, v4, result);
  result = mkIte(c3, v3, result);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

SMTExprRef SMTFPSolver::mkSBVtoFPImpl(const SMTExprRef &From,
                                      const SMTSortRef &To, const RM &R) {
  // This is a conversion from unsigned bitvector to float:
  // ((_ to_fp_unsigned eb sb) RM (_ BitVec m) (_ FloatingPoint eb
  // sb)) Semantics:
  //    Let b in[[(_ BitVec m)]] and let n be the unsigned integer represented
  //    by b.
  //    [[(_ to_fp_unsigned eb sb)]](r, x) = +infinity if n is too large to be
  //    represented as a finite number of[[(_ FloatingPoint eb sb)]];
  //    [[(_ to_fp_unsigned eb sb)]](r, x) = y otherwise, where y is the finite
  //    number such that[[fp.to_real]](y) is closest to n according to rounding
  //    mode r.

  unsigned ebits = To->getFPExponentWidth();
  unsigned sbits = To->getFPSignificandWidth();
  unsigned bv_sz = From->getWidth();

  SMTExprRef bv1_1 = mkBVFromDec(1, 1);
  SMTExprRef bv0_sz = mkBVFromDec(0, bv_sz);

  SMTExprRef is_zero = mkEqual(From, bv0_sz);

  SMTExprRef pzero = mkPZero(*this, ebits, sbits);

  // Special case: x == 0 -> p/n zero
  SMTExprRef c1 = is_zero;
  SMTExprRef v1 = pzero;

  // Special case: x != 0
  SMTExprRef is_neg_bit = mkBVExtract(bv_sz - 1, bv_sz - 1, From);
  SMTExprRef is_neg = mkEqual(is_neg_bit, bv1_1);
  SMTExprRef neg_x = mkBVNeg(From);
  SMTExprRef x_abs = mkIte(is_neg, neg_x, From);

  // x is [bv_sz-1] . [bv_sz-2 ... 0] * 2^(bv_sz-1)
  // bv_sz-1 is the "1.0" bit for the rounder.

  SMTExprRef lz = mkLeadingZeros(*this, x_abs, bv_sz);
  SMTExprRef shifted_sig = mkBVShl(x_abs, lz);

  // shifted_sig is [bv_sz-1, bv_sz-2] . [bv_sz-3 ... 0] * 2^(bv_sz-2) * 2^(-lz)
  unsigned sig_sz = sbits + 4; // we want extra rounding bits.

  SMTExprRef sig_4, sticky;
  if (sig_sz <= bv_sz) {
    // one short
    sig_4 = mkBVExtract(bv_sz - 1, bv_sz - sig_sz + 1, shifted_sig);

    SMTExprRef sig_rest = mkBVExtract(bv_sz - sig_sz, 0, shifted_sig);
    sticky = mkBVRedOr(sig_rest);
    sig_4 = mkBVConcat(sig_4, sticky);
  } else {
    unsigned extra_bits = sig_sz - bv_sz;
    SMTExprRef extra_zeros = mkBVFromDec(0, extra_bits);
    sig_4 = mkBVConcat(shifted_sig, extra_zeros);
    lz = mkBVAdd(mkBVConcat(extra_zeros, lz), mkBVFromDec(extra_bits, sig_sz));
    bv_sz = bv_sz + extra_bits;
  }
  assert(sig_4->getWidth() == sig_sz);

  SMTExprRef s_exp = mkBVSub(mkBVFromDec(bv_sz - 2, bv_sz), lz);

  // s_exp = (bv_sz-2) + (-lz) signed
  assert(s_exp->getWidth() == bv_sz);

  unsigned exp_sz = ebits + 2; // (+2 for rounder)
  SMTExprRef exp_2 = mkBVExtract(exp_sz - 1, 0, s_exp);

  // the remaining bits are 0 if ebits is large enough.
  SMTExprRef exp_too_large = mkBool(false);

  // The exponent is at most bv_sz, i.e., we need ld(bv_sz)+1 ebits.
  // exp < bv_sz (+sign bit which is [0])
  unsigned exp_worst_case_sz =
      (unsigned)((log((double)bv_sz) / log((double)2)) + 1.0);

  if (exp_sz < exp_worst_case_sz) {
    // exp_sz < exp_worst_case_sz and exp >= 0.
    // Take the maximum legal exponent; this
    // allows us to keep the most precision.
    SMTExprRef max_exp = mkMaxExp(*this, exp_sz);
    SMTExprRef max_exp_bvsz = mkBVZeroExt(bv_sz - exp_sz, max_exp);

    exp_too_large =
        mkBVSle(mkBVAdd(max_exp_bvsz, mkBVFromDec(1, bv_sz)), s_exp);
    SMTExprRef zero_sig_sz = mkBVFromDec(0, sig_sz);
    sig_4 = mkIte(exp_too_large, zero_sig_sz, sig_4);
    exp_2 = mkIte(exp_too_large, max_exp, exp_2);
  }

  SMTExprRef sgn, sig, exp;
  sgn = is_neg_bit;
  sig = sig_4;
  exp = exp_2;

  assert(sig->getWidth() == sbits + 4);
  assert(exp->getWidth() == ebits + 2);

  SMTExprRef rm = mkRM(R);
  SMTExprRef v2 = round(rm, sgn, sig, exp, ebits, sbits);
  return mkIte(c1, v1, v2);
}

SMTExprRef SMTFPSolver::mkUBVtoFPImpl(const SMTExprRef &From,
                                      const SMTSortRef &To, const RM &R) {
  // This is a conversion from unsigned bitvector to float:
  // ((_ to_fp_unsigned eb sb) RM (_ BitVec m) (_ FloatingPoint eb
  // sb)) Semantics:
  //    Let b in[[(_ BitVec m)]] and let n be the unsigned integer represented
  //    by b.
  //    [[(_ to_fp_unsigned eb sb)]](r, x) = +infinity if n is too large to be
  //    represented as a finite number of[[(_ FloatingPoint eb sb)]];
  //    [[(_ to_fp_unsigned eb sb)]](r, x) = y otherwise, where y is the finite
  //    number such that[[fp.to_real]](y) is closest to n according to rounding
  //    mode r.

  unsigned ebits = To->getFPExponentWidth();
  unsigned sbits = To->getFPSignificandWidth();
  unsigned bv_sz = From->getWidth();

  SMTExprRef bv0_1 = mkBVFromDec(0, 1);
  SMTExprRef bv0_sz = mkBVFromDec(0, bv_sz);

  SMTExprRef is_zero = mkEqual(From, bv0_sz);

  SMTExprRef pzero = mkPZero(*this, ebits, sbits);

  // Special case: x == 0 -> p/n zero
  SMTExprRef c1 = is_zero;
  SMTExprRef v1 = pzero;

  // Special case: x != 0
  // x is [bv_sz-1] . [bv_sz-2 ... 0] * 2^(bv_sz-1)
  // bv_sz-1 is the "1.0" bit for the rounder.

  SMTExprRef lz = mkLeadingZeros(*this, From, bv_sz);
  SMTExprRef shifted_sig = mkBVShl(From, lz);

  // shifted_sig is [bv_sz-1] . [bv_sz-2 ... 0] * 2^(bv_sz-1) * 2^(-lz)
  unsigned sig_sz = sbits + 4; // we want extra rounding bits.

  SMTExprRef sig_4, sticky;
  if (sig_sz <= bv_sz) {
    // one short
    sig_4 = mkBVExtract(bv_sz - 1, bv_sz - sig_sz + 1, shifted_sig);

    SMTExprRef sig_rest = mkBVExtract(bv_sz - sig_sz, 0, shifted_sig);
    sticky = mkBVRedOr(sig_rest);
    sig_4 = mkBVConcat(sig_4, sticky);
  } else {
    unsigned extra_bits = sig_sz - bv_sz;
    SMTExprRef extra_zeros = mkBVFromDec(0, extra_bits);
    sig_4 = mkBVConcat(shifted_sig, extra_zeros);
    lz = mkBVAdd(mkBVConcat(extra_zeros, lz), mkBVFromDec(extra_bits, sig_sz));
    bv_sz = bv_sz + extra_bits;
  }
  assert(sig_4->getWidth() == sig_sz);

  SMTExprRef s_exp = mkBVSub(mkBVFromDec(bv_sz - 2, bv_sz), lz);

  // s_exp = (bv_sz-2) + (-lz) signed
  assert(s_exp->getWidth() == bv_sz);

  unsigned exp_sz = ebits + 2; // (+2 for rounder)
  SMTExprRef exp_2 = mkBVExtract(exp_sz - 1, 0, s_exp);

  // the remaining bits are 0 if ebits is large enough.
  SMTExprRef exp_too_large = mkBool(false); // This is always in range.

  // The exponent is at most bv_sz, i.e., we need ld(bv_sz)+1 ebits.
  // exp < bv_sz (+sign bit which is [0])
  unsigned exp_worst_case_sz =
      (unsigned)((log((double)bv_sz) / log((double)2)) + 1.0);

  if (exp_sz < exp_worst_case_sz) {
    // exp_sz < exp_worst_case_sz and exp >= 0.
    // Take the maximum legal exponent; this
    // allows us to keep the most precision.
    SMTExprRef max_exp = mkMaxExp(*this, exp_sz);
    SMTExprRef max_exp_bvsz = mkBVZeroExt(bv_sz - exp_sz, max_exp);

    exp_too_large =
        mkBVSle(mkBVAdd(max_exp_bvsz, mkBVFromDec(1, bv_sz)), s_exp);
    SMTExprRef zero_sig_sz = mkBVFromDec(0, sig_sz);
    sig_4 = mkIte(exp_too_large, zero_sig_sz, sig_4);
    exp_2 = mkIte(exp_too_large, max_exp, exp_2);
  }

  SMTExprRef sgn, sig, exp;
  sgn = bv0_1;
  sig = sig_4;
  exp = exp_2;

  assert(sig->getWidth() == sbits + 4);
  assert(exp->getWidth() == ebits + 2);

  SMTExprRef rm = mkRM(R);
  SMTExprRef v2 = round(rm, sgn, sig, exp, ebits, sbits);
  return mkIte(c1, v1, v2);
}

SMTExprRef SMTFPSolver::mkToBV(SMTExprRef Exp, bool isSigned,
                               unsigned int ToWidth) {
  SMTExprRef rm = mkRM(RM::ROUND_TO_ZERO);
  SMTSortRef xs = Exp->Sort;

  unsigned ebits = xs->getFPExponentWidth();
  unsigned sbits = xs->getFPSignificandWidth();
  unsigned bv_sz = ToWidth;

  SMTExprRef bv0 = mkBVFromDec(0, 1);
  SMTExprRef bv1 = mkBVFromDec(1, 1);

  SMTExprRef x_is_nan = mkFPIsNaN(Exp);
  SMTExprRef x_is_inf = mkFPIsInfinite(Exp);
  SMTExprRef x_is_zero = mkFPIsZero(Exp);
  SMTExprRef x_is_neg = mkIsNeg(*this, Exp);

  // NaN, Inf, or negative (except -0) -> unspecified
  SMTExprRef c1 = mkOr(x_is_nan, x_is_inf);
  SMTExprRef unspec_v = mkSymbol("UNSPEC_FP", getBVSort(ToWidth));
  SMTExprRef v1 = unspec_v;

  // +-0 -> 0
  SMTExprRef c2 = x_is_zero;
  SMTExprRef v2 = mkBVFromDec(0, ToWidth);

  // Otherwise...
  SMTExprRef sgn, sig, exp, lz;
  unpack(*this, Exp, sgn, sig, exp, lz, true);

  // sig is of the form +- [1].[sig] * 2^(exp-lz)
  assert(sgn->getWidth() == 1);
  assert(sig->getWidth() == sbits);
  assert(exp->getWidth() == ebits);
  assert(lz->getWidth() == ebits);

  unsigned sig_sz = sbits;
  if (sig_sz < (bv_sz + 3))
    sig = mkBVConcat(sig, mkBVFromDec(0, bv_sz - sig_sz + 3));
  sig_sz = sig->getWidth();
  assert(sig_sz >= (bv_sz + 3));

  // x is of the form +- [1].[sig][r][g][s] ... and at least bv_sz + 3 long
  SMTExprRef exp_m_lz = mkBVSub(mkBVSignExt(2, exp), mkBVZeroExt(2, lz));

  // big_sig is +- [... bv_sz+2 bits ...][1].[r][ ... sbits-1  ... ]
  SMTExprRef big_sig = mkBVConcat(mkBVZeroExt(bv_sz + 2, sig), bv0);
  unsigned big_sig_sz = sig_sz + 1 + bv_sz + 2;
  assert(big_sig->getWidth() == big_sig_sz);

  SMTExprRef is_neg_shift = mkBVSle(exp_m_lz, mkBVFromDec(0, ebits + 2));
  SMTExprRef shift = mkIte(is_neg_shift, mkBVNeg(exp_m_lz), exp_m_lz);
  if (ebits + 2 < big_sig_sz)
    shift = mkBVZeroExt(big_sig_sz - ebits - 2, shift);
  else if (ebits + 2 > big_sig_sz) {
    SMTExprRef upper = mkBVExtract(big_sig_sz, ebits + 2, shift);
    shift = mkBVExtract(ebits + 1, 0, shift);
    shift = mkIte(mkEqual(upper, mkBVFromDec(0, upper->getWidth())), shift,
                  mkBVFromDec(big_sig_sz - 1, ebits + 2));
  }
  assert(shift->getWidth() == big_sig->getWidth());

  SMTExprRef shift_limit = mkBVFromDec(bv_sz + 2, shift->getWidth());
  shift = mkIte(mkBVUle(shift, shift_limit), shift, shift_limit);

  SMTExprRef big_sig_shifted =
      mkIte(is_neg_shift, mkBVLshr(big_sig, shift), mkBVShl(big_sig, shift));
  SMTExprRef int_part =
      mkBVExtract(big_sig_sz - 1, big_sig_sz - (bv_sz + 3), big_sig_shifted);
  assert(int_part->getWidth() == bv_sz + 3);
  SMTExprRef last = mkBVExtract(big_sig_sz - (bv_sz + 3),
                                big_sig_sz - (bv_sz + 3), big_sig_shifted);
  SMTExprRef round = mkBVExtract(big_sig_sz - (bv_sz + 4),
                                 big_sig_sz - (bv_sz + 4), big_sig_shifted);
  SMTExprRef stickies =
      mkBVExtract(big_sig_sz - (bv_sz + 5), 0, big_sig_shifted);
  SMTExprRef sticky = mkBVRedOr(stickies);

  SMTExprRef rounding_decision =
      mkRoundingDecision(*this, rm, sgn, last, round, sticky);
  assert(rounding_decision->getWidth() == 1);

  SMTExprRef inc = mkBVZeroExt(bv_sz + 2, rounding_decision);
  SMTExprRef pre_rounded = mkBVAdd(int_part, inc);

  SMTExprRef incd = mkEqual(rounding_decision, bv1);
  SMTExprRef pr_is_zero = mkEqual(pre_rounded, mkBVFromDec(0, bv_sz + 3));
  SMTExprRef ovfl = mkAnd(incd, pr_is_zero);

  SMTExprRef ul, in_range;
  if (!isSigned) {
    ul = mkBVZeroExt(3, mkBVNeg(mkBVFromDec(1, bv_sz)));
    in_range =
        mkAnd(mkAnd(mkOr(mkNot(x_is_neg),
                         mkEqual(pre_rounded, mkBVFromDec(0, bv_sz + 3))),
                    mkNot(ovfl)),
              mkBVUle(pre_rounded, ul));
  } else {
    SMTExprRef ll = mkBVSignExt(3, mkBVConcat(bv1, mkBVFromDec(0, bv_sz - 1)));
    ul = mkBVZeroExt(4, mkBVNeg(mkBVFromDec(1, bv_sz - 1)));
    ovfl = mkOr(ovfl, mkBVSle(pre_rounded, mkBVNeg(mkBVFromDec(1, bv_sz + 3))));
    pre_rounded = mkIte(x_is_neg, mkBVNeg(pre_rounded), pre_rounded);
    in_range = mkAnd(mkAnd(mkNot(ovfl), mkBVSle(ll, pre_rounded)),
                     mkBVSle(pre_rounded, ul));
  }

  SMTExprRef rounded = mkBVExtract(bv_sz - 1, 0, pre_rounded);

  SMTExprRef result = mkIte(mkNot(in_range), unspec_v, rounded);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

SMTExprRef SMTFPSolver::mkFPtoSBVImpl(const SMTExprRef &From,
                                      unsigned ToWidth) {
  return mkToBV(From, true, ToWidth);
}

SMTExprRef SMTFPSolver::mkFPtoUBVImpl(const SMTExprRef &From,
                                      unsigned ToWidth) {
  return mkToBV(From, false, ToWidth);
}

SMTExprRef SMTFPSolver::mkFPtoIntegralImpl(const SMTExprRef &From, RM R) {
  unsigned ebits = From->Sort->getFPExponentWidth();
  unsigned sbits = From->Sort->getFPSignificandWidth();

  SMTExprRef rm = mkRM(R);
  SMTExprRef rm_is_rta = mkIsRM(*this, rm, RM::ROUND_TO_AWAY);
  SMTExprRef rm_is_rte = mkIsRM(*this, rm, RM::ROUND_TO_EVEN);
  SMTExprRef rm_is_rtp = mkIsRM(*this, rm, RM::ROUND_TO_PLUS_INF);
  SMTExprRef rm_is_rtn = mkIsRM(*this, rm, RM::ROUND_TO_MINUS_INF);
  SMTExprRef rm_is_rtz = mkIsRM(*this, rm, RM::ROUND_TO_ZERO);

  SMTExprRef nzero = mkNZero(*this, ebits, sbits);
  SMTExprRef pzero = mkPZero(*this, ebits, sbits);

  SMTExprRef x_is_neg = mkIsNeg(*this, From);

  // (x is NaN) -> NaN
  SMTExprRef c1 = mkFPIsNaN(From);
  SMTExprRef v1 = From;

  // (x is +-oo) -> x
  SMTExprRef c2 = mkFPIsInfinite(From);
  SMTExprRef v2 = From;

  // (x is +-0) -> x ; -0.0 -> -0.0, says IEEE754, Sec 5.9.
  SMTExprRef c3 = mkFPIsZero(From);
  SMTExprRef v3 = From;

  SMTExprRef one_1 = mkBVFromDec(1, 1);
  SMTExprRef zero_1 = mkBVFromDec(0, 1);

  SMTExprRef a_sgn, a_sig, a_exp, a_lz;
  unpack(*this, From, a_sgn, a_sig, a_exp, a_lz, true);

  SMTExprRef sgn_eq_1 = mkEqual(a_sgn, one_1);
  SMTExprRef xzero = mkIte(sgn_eq_1, nzero, pzero);

  // exponent < 0 -> 0/1
  SMTExprRef exp_h = mkBVExtract(ebits - 1, ebits - 1, a_exp);
  SMTExprRef exp_lt_zero = mkEqual(exp_h, one_1);
  SMTExprRef c4 = exp_lt_zero;

  SMTExprRef pone = mkOne(*this, zero_1, ebits, sbits);
  SMTExprRef none = mkOne(*this, one_1, ebits, sbits);
  SMTExprRef xone = mkIte(sgn_eq_1, none, pone);

  SMTExprRef pow_2_sbitsm1 = mkBVFromDec(power2(sbits - 1, false), sbits);
  SMTExprRef m1 = mkBVNeg(mkBVFromDec(1, ebits));
  SMTExprRef t1 = mkEqual(a_sig, pow_2_sbitsm1);
  SMTExprRef t2 = mkEqual(a_exp, m1);
  SMTExprRef tie = mkAnd(t1, t2);

  SMTExprRef c421 = mkAnd(tie, rm_is_rte);
  SMTExprRef c422 = mkAnd(tie, rm_is_rta);
  SMTExprRef c423 = mkBVSle(a_exp, mkBVNeg(mkBVFromDec(2, ebits)));

  SMTExprRef v42 = xone;
  v42 = mkIte(c423, xzero, v42);
  v42 = mkIte(c422, xone, v42);
  v42 = mkIte(c421, xzero, v42);

  SMTExprRef v4_rtp = mkIte(x_is_neg, nzero, pone);
  SMTExprRef v4_rtn = mkIte(x_is_neg, none, pzero);

  SMTExprRef v4 = mkIte(rm_is_rtp, v4_rtp, v42);
  v4 = mkIte(rm_is_rtn, v4_rtn, v4);
  v4 = mkIte(rm_is_rtz, xzero, v4);

  // exponent >= sbits-1 -> x
  SMTExprRef exp_is_large = log2(sbits - 1) + 1 <= ebits - 1
                                ? mkBVSle(mkBVFromDec(sbits - 1, ebits), a_exp)
                                : mkBool(false);
  SMTExprRef c5 = exp_is_large;
  SMTExprRef v5 = From;

  // Actual conversion with rounding.
  // exponent >= 0 && exponent < sbits - 1
  SMTExprRef res_sgn = a_sgn;
  SMTExprRef res_exp = a_exp;

  assert(a_sig->getWidth() == sbits);
  assert(a_exp->getWidth() == ebits);

  SMTExprRef zero_s = mkBVFromDec(0, sbits);

  SMTExprRef shift =
      mkBVSub(mkBVFromDec(sbits - 1, sbits), mkBVZeroExt(sbits - ebits, a_exp));
  SMTExprRef shifted_sig =
      mkBVLshr(mkBVConcat(a_sig, zero_s), mkBVConcat(zero_s, shift));
  SMTExprRef div = mkBVExtract(2 * sbits - 1, sbits, shifted_sig);
  SMTExprRef rem = mkBVExtract(sbits - 1, 0, shifted_sig);

  assert(shift->getWidth() == sbits);
  assert(div->getWidth() == sbits);
  assert(rem->getWidth() == sbits);

  SMTExprRef div_p1 = mkBVAdd(div, mkBVFromDec(1, sbits));

  SMTExprRef tie_pttrn = mkBVConcat(one_1, mkBVFromDec(0, sbits - 1));
  SMTExprRef tie2 = mkEqual(rem, tie_pttrn);
  SMTExprRef div_last = mkBVExtract(0, 0, div);
  SMTExprRef div_last_eq_1 = mkEqual(div_last, one_1);
  SMTExprRef rte_and_dl_eq_1 = mkAnd(rm_is_rte, div_last_eq_1);
  SMTExprRef rte_and_dl_eq_1_or_rta = mkOr(rte_and_dl_eq_1, rm_is_rta);
  SMTExprRef tie_pttrn_ule_rem = mkBVUle(tie_pttrn, rem);
  SMTExprRef tie2_c = mkIte(tie2, rte_and_dl_eq_1_or_rta, tie_pttrn_ule_rem);
  SMTExprRef v51 = mkIte(tie2_c, div_p1, div);

  SMTExprRef rem_eq_0 = mkEqual(rem, mkBVFromDec(0, sbits));
  SMTExprRef sgn_eq_zero = mkEqual(res_sgn, zero_1);
  SMTExprRef c521 = mkNot(rem_eq_0);
  c521 = mkAnd(c521, sgn_eq_zero);
  SMTExprRef v52 = mkIte(c521, div_p1, div);

  SMTExprRef sgn_eq_one = mkEqual(res_sgn, one_1);
  SMTExprRef c531 = mkNot(rem_eq_0);
  c531 = mkAnd(c531, sgn_eq_one);
  SMTExprRef v53 = mkIte(c531, div_p1, div);

  SMTExprRef c51 = mkOr(rm_is_rte, rm_is_rta);
  SMTExprRef c52 = rm_is_rtp;
  SMTExprRef c53 = rm_is_rtn;

  SMTExprRef res_sig = div;
  res_sig = mkIte(c53, v53, res_sig);
  res_sig = mkIte(c52, v52, res_sig);
  res_sig = mkIte(c51, v51, res_sig);

  assert(res_exp->getWidth() == ebits);
  assert(shift->getWidth() == sbits);

  SMTExprRef e_shift = (ebits + 2 <= sbits + 1)
                           ? mkBVExtract(ebits + 1, 0, shift)
                           : mkBVSignExt((ebits + 2) - (sbits), shift);
  assert(e_shift->getWidth() == ebits + 2);
  res_exp = mkBVAdd(mkBVZeroExt(2, res_exp), e_shift);

  assert(res_sgn->getWidth() == 1);
  assert(res_sig->getWidth() == sbits);
  assert(res_exp->getWidth() == ebits + 2);

  // Renormalize
  SMTExprRef zero_e2 = mkBVFromDec(0, ebits + 2);
  SMTExprRef min_exp = mkMinExp(*this, ebits);
  min_exp = mkBVSignExt(2, min_exp);
  SMTExprRef sig_lz = mkLeadingZeros(*this, res_sig, ebits + 2);
  SMTExprRef max_exp_delta = mkBVSub(res_exp, min_exp);
  SMTExprRef sig_lz_capped =
      mkIte(mkBVSle(sig_lz, max_exp_delta), sig_lz, max_exp_delta);
  SMTExprRef renorm_delta =
      mkIte(mkBVSle(zero_e2, sig_lz_capped), sig_lz_capped, zero_e2);
  assert(renorm_delta->getWidth() == ebits + 2);
  res_exp = mkBVSub(res_exp, renorm_delta);
  res_sig = mkBVShl(res_sig, mkBVZeroExt(sbits - ebits - 2, renorm_delta));

  res_exp = mkBVExtract(ebits - 1, 0, res_exp);
  res_exp = mkBias(*this, res_exp);
  res_sig = mkBVExtract(sbits - 2, 0, res_sig);
  SMTExprRef v6 =
      mkBVToIEEEFP(mkBVConcat(res_sgn, mkBVConcat(res_exp, res_sig)),
                   getFPSort(ebits, sbits - 1));

  // And finally, we tie them together.
  SMTExprRef result = mkIte(c5, v5, v6);
  result = mkIte(c4, v4, result);
  result = mkIte(c3, v3, result);
  result = mkIte(c2, v2, result);
  return mkIte(c1, v1, result);
}

template <typename FPType>
static inline FPType getFPValue(SMTFPSolver &S, const SMTExprRef &Exp) {
  unsigned int ebits = Exp->Sort->getFPExponentWidth();
  unsigned int sbits = Exp->Sort->getFPSignificandWidth();

  // Extract parts
  int64_t sgn = S.getBV(extractSgn(S, Exp));
  int64_t exp = S.getBV(extractExp(S, Exp));
  int64_t sig = S.getBV(extractSig(S, Exp));

  // In our circuits the hidden bit is visible, so remove it
  sig &= power2m1(sbits, false);

  if (power2m1(ebits, false) == exp) {
    // This is either a NaN
    if (sig)
      return sgn ? -NAN : NAN;

    // or an inf
    return sgn ? -INFINITY : INFINITY;
  }

  FPType result;
  memcpy(&result, &sig, sizeof(FPType));
  return result;
}

std::string SMTFPSolver::getFPInBinImpl(const SMTExprRef &Exp) {
  return getBVInBin(Exp);
}

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

SMTExprRef SMTFPSolver::mkFPFromBinImpl(const std::string &FP,
                                        unsigned EWidth) {
  return mkBVFromBin(FP, getFPSort(EWidth, FP.length() - EWidth - 1));
}

SMTExprRef SMTFPSolver::mkRMImpl(const RM &R) {
  return mkBVFromDec(static_cast<int64_t>(R), getRMSort());
}

SMTExprRef SMTFPSolver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  // we always create the same NaN: sgn = Sgn, exp = all 1, sig = 0...01
  SMTExprRef top_exp = mkTopExp(*this, ExpWidth);
  return mkBVToIEEEFP(mkBVConcat(mkBVFromDec(Sgn, 1),
                                 mkBVConcat(top_exp, mkBVFromDec(1, SigWidth))),
                      getFPSort(ExpWidth, SigWidth));
}

SMTExprRef SMTFPSolver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  SMTExprRef top_exp = mkTopExp(*this, ExpWidth);
  return mkBVToIEEEFP(mkBVConcat(mkBVFromDec(Sgn, 1),
                                 mkBVConcat(top_exp, mkBVFromDec(0, SigWidth))),
                      getFPSort(ExpWidth, SigWidth));
}

SMTExprRef SMTFPSolver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                         const SMTSortRef &To) {
  Exp->Sort = To;
  return Exp;
}

SMTExprRef SMTFPSolver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  // Do nothing, it's already a bitvector
  return Exp;
}

SMTExprRef SMTFPSolver::round(SMTExprRef &R, SMTExprRef &Sgn, SMTExprRef &Sig,
                              SMTExprRef &Exp, unsigned EWidth,
                              unsigned SWidth) {
  // Assumptions: sig is of the form f[-1:0] . f[1:SWidth-1]
  // [guard,round,sticky],
  // i.e., it has 2 + (SWidth-1) + 3 = SWidth + 4 bits, where the first one is
  // in sgn. Furthermore, note that sig is an unsigned bit-vector, while exp is
  // signed.

  assert(R->getWidth() == 3);
  assert(Sgn->getWidth() == 1);
  assert(Sig->getWidth() >= 5);
  assert(Exp->getWidth() >= 4);

  assert(Sig->getWidth() == SWidth + 4);
  assert(Exp->getWidth() == EWidth + 2);

  SMTExprRef e_min = mkMinExp(*this, EWidth);
  SMTExprRef e_max = mkMaxExp(*this, EWidth);

  SMTExprRef one_1 = mkBVFromDec(1, 1);
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

  SMTExprRef t = mkBVAdd(Exp, mkBVFromDec(1, EWidth + 2));
  t = mkBVSub(t, lz);
  t = mkBVSub(t, mkBVSignExt(2, e_min));
  SMTExprRef TINY = mkBVSle(t, mkBVFromDec(ULLONG_MAX, EWidth + 2));

  SMTExprRef beta = mkBVAdd(mkBVSub(Exp, lz), mkBVFromDec(1, EWidth + 2));

  SMTExprRef sigma_add = mkBVSub(Exp, mkBVSignExt(2, e_min));
  sigma_add = mkBVAdd(sigma_add, mkBVFromDec(1, EWidth + 2));
  SMTExprRef sigma = mkIte(TINY, sigma_add, lz);

  // Normalization shift
  std::size_t sig_size = Sig->getWidth();
  assert(sig_size == SWidth + 4);
  assert(sigma->getWidth() == EWidth + 2);
  std::size_t sigma_size = EWidth + 2;

  SMTExprRef sigma_neg = mkBVNeg(sigma);
  SMTExprRef sigma_cap = mkBVFromDec(SWidth + 2, sigma_size);
  SMTExprRef sigma_le_cap = mkBVUle(sigma_neg, sigma_cap);
  SMTExprRef sigma_neg_capped = mkIte(sigma_le_cap, sigma_neg, sigma_cap);
  SMTExprRef sigma_lt_zero =
      mkBVSle(sigma, mkBVFromDec(ULLONG_MAX, sigma_size));

  SMTExprRef sig_ext = mkBVConcat(Sig, mkBVFromDec(0, sig_size));
  SMTExprRef rs_sig = mkBVLshr(
      sig_ext, mkBVZeroExt(2 * sig_size - sigma_size, sigma_neg_capped));
  SMTExprRef ls_sig =
      mkBVShl(sig_ext, mkBVZeroExt(2 * sig_size - sigma_size, sigma));
  SMTExprRef big_sh_sig = mkIte(sigma_lt_zero, rs_sig, ls_sig);
  assert(big_sh_sig->getWidth() == 2 * sig_size);

  std::size_t sig_extract_low_bit = (2 * sig_size - 1) - (SWidth + 2) + 1;
  Sig = mkBVExtract(2 * sig_size - 1, sig_extract_low_bit, big_sh_sig);
  assert(Sig->getWidth() == SWidth + 2);

  SMTExprRef sticky =
      mkBVRedOr(mkBVExtract(sig_extract_low_bit - 1, 0, big_sh_sig));

  // put the sticky bit into the significand.
  SMTExprRef ext_sticky = mkBVZeroExt(SWidth + 1, sticky);
  Sig = mkBVOr(Sig, ext_sticky);
  assert(Sig->getWidth() == SWidth + 2);

  SMTExprRef ext_emin = mkBVZeroExt(2, e_min);
  Exp = mkIte(TINY, ext_emin, beta);

  // Significand rounding
  sticky = mkBVExtract(0, 0, Sig); // new sticky bit!
  SMTExprRef round = mkBVExtract(1, 1, Sig);
  SMTExprRef last = mkBVExtract(2, 2, Sig);

  Sig = mkBVExtract(SWidth + 1, 2, Sig);

  SMTExprRef inc = mkRoundingDecision(*this, R, Sgn, last, round, sticky);
  assert(inc->getWidth() == 1);

  Sig = mkBVAdd(mkBVZeroExt(1, Sig), mkBVZeroExt(SWidth, inc));

  // Post normalization
  assert(Sig->getWidth() == SWidth + 1);
  t_sig = mkBVExtract(SWidth, SWidth, Sig);
  SMTExprRef SIGovf = mkEqual(t_sig, one_1);

  SMTExprRef hallbut1_sig = mkBVExtract(SWidth, 1, Sig);
  SMTExprRef lallbut1_sig = mkBVExtract(SWidth - 1, 0, Sig);
  Sig = mkIte(SIGovf, hallbut1_sig, lallbut1_sig);

  assert(Exp->getWidth() == EWidth + 2);

  SMTExprRef exp_p1 = mkBVAdd(Exp, mkBVFromDec(1, EWidth + 2));
  Exp = mkIte(SIGovf, exp_p1, Exp);

  assert(Sig->getWidth() == SWidth);
  assert(Exp->getWidth() == EWidth + 2);
  assert(e_max->getWidth() == EWidth);

  // Exponent adjustment and rounding
  SMTExprRef biased_exp = mkBias(*this, mkBVExtract(EWidth - 1, 0, Exp));

  // AdjustExp
  assert(OVF1->Sort->isBoolSort());

  SMTExprRef exp_redand = mkBVRedAnd(biased_exp);
  SMTExprRef preOVF2 = mkEqual(exp_redand, one_1);
  SMTExprRef OVF2 = mkAnd(SIGovf, preOVF2);
  SMTExprRef pem2m1 = mkBVFromDec(power2m1(EWidth - 2, false), EWidth);
  biased_exp = mkIte(OVF2, pem2m1, biased_exp);
  SMTExprRef OVF = mkOr(OVF1, OVF2);

  assert(OVF2->Sort->isBoolSort());
  assert(OVF->Sort->isBoolSort());

  // ExpRnd
  SMTExprRef top_exp = mkTopExp(*this, EWidth);
  SMTExprRef bot_exp = mkBotExp(*this, EWidth);

  SMTExprRef nil_1 = mkBVFromDec(0, 1);

  SMTExprRef rm_is_to_zero = mkIsRM(*this, R, RM::ROUND_TO_ZERO);
  SMTExprRef rm_is_to_neg = mkIsRM(*this, R, RM::ROUND_TO_MINUS_INF);
  SMTExprRef rm_is_to_pos = mkIsRM(*this, R, RM::ROUND_TO_PLUS_INF);
  SMTExprRef rm_zero_or_neg = mkOr(rm_is_to_zero, rm_is_to_neg);
  SMTExprRef rm_zero_or_pos = mkOr(rm_is_to_zero, rm_is_to_pos);

  SMTExprRef zero1 = mkBVFromDec(0, 1);
  SMTExprRef sgn_is_zero = mkEqual(Sgn, zero1);

  SMTExprRef max_sig = mkBVFromDec(power2m1(SWidth - 1, false), SWidth - 1);
  SMTExprRef max_exp = mkBVConcat(
      mkBVFromDec(power2m1(EWidth - 1, false), EWidth - 1), mkBVFromDec(0, 1));
  SMTExprRef inf_sig = mkBVFromDec(0, SWidth - 1);
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

  assert(Sgn->getWidth() == 1);
  assert(Sig->getWidth() == SWidth - 1);
  assert(Exp->getWidth() == EWidth);

  return mkBVToIEEEFP(mkBVConcat(Sgn, mkBVConcat(Exp, Sig)),
                      getFPSort(EWidth, SWidth - 1));
}
