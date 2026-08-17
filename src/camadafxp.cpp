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

// Fixed-point arithmetic, encoded over bit-vectors in the common layer.
//
// The semantic target is C fixed-point (ISO/IEC TR 18037) as consumed by a
// verifier: a fixed-point value of width W with N fractional bits is the
// rational raw/2^N with `raw` two's complement when signed. Non-saturating
// overflow is undefined behavior in C, so every operation that can overflow
// has a companion predicate reporting exactly the UB condition, and the BV
// value an operation produces is meaningful only under the negation of its
// predicate. Overflow predicates for multiplication, division, and
// fixed-to-fixed conversion test the *pre-rounding* exact result — an exact
// result just outside the representable range must be reported even when
// truncation would land it back on a boundary. Fixed-point to integer
// conversion rounds toward zero (the one direction TR 18037 specifies);
// everything else — multiplication, division, and narrowing — rounds down
// (floor), matching Clang's implementation-defined choices as pinned by
// the execution oracle (scripts/fxp_oracle_gen.py).
//
// Mixed-format operands: TR 18037 states the usual arithmetic conversions
// do NOT apply between fixed-point operands — the operation is computed
// "with the full precision of both operands" and only the RESULT is
// converted, to the higher-ranked operand type (6.3.1.8 as amended; all
// accums outrank all fracts, signed wins sign mixes — verified against
// Clang across 8781 oracle vectors). Camada implements the full-precision
// half: mixed operands compute exactly in the common containing format
// (max integer bits, max fractional bits, signed if either side is) and
// the result CARRIES that common format, not C's ranked result type.
// Consumers implementing C semantics convert explicitly:
//   mkFXPToFXP[Sat](mixed-op result, C-result-sort)
// which is exact (floor composes across nested scales; clamps compose
// monotonically) — pinned end-to-end by the kMixed oracle fixtures.
//
// No solver has a native fixed-point theory, so unlike camadafp.cpp there is
// no native-vs-encoded split here: everything below is built once from the
// public BV surface and works on every backend, including the SMT-LIB pipe.

#include "camadaimpl.h"

#include "camadacommon.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace camada {

namespace {

// ---------------------------------------------------------------------------
// Format and constant helpers
// ---------------------------------------------------------------------------

struct FXPFormat {
  unsigned Width = 0;
  unsigned FracBits = 0;
  bool IsSigned = false;

  unsigned intBits() const { return Width - FracBits - (IsSigned ? 1 : 0); }
};

FXPFormat formatOf(const SMTSortRef &Sort) {
  return FXPFormat{Sort->getWidth(), Sort->getFXPFracBits(),
                   Sort->isFXPSignedSort()};
}

// The common full-precision format of two operand formats (TR 18037 usual
// arithmetic conversions): enough integer bits and fraction bits to hold
// either operand exactly, signed if either side is signed.
FXPFormat commonFormat(const FXPFormat &A, const FXPFormat &B) {
  FXPFormat C;
  C.IsSigned = A.IsSigned || B.IsSigned;
  unsigned IntBits = std::max(A.intBits(), B.intBits());
  C.FracBits = std::max(A.FracBits, B.FracBits);
  C.Width = IntBits + C.FracBits + (C.IsSigned ? 1 : 0);
  return C;
}

// Bounds are built as binary strings so any width works.

// Two's-complement binary string of the format's largest raw value, widened
// to TotalWidth and shifted left by Shift zero bits.
std::string maxRawBits(const FXPFormat &F, unsigned TotalWidth,
                       unsigned Shift = 0) {
  // max = 2^(Width-1)-1 signed, 2^Width-1 unsigned.
  unsigned Ones = F.IsSigned ? F.Width - 1 : F.Width;
  std::string Bits(TotalWidth, '0');
  for (unsigned I = 0; I < Ones; ++I)
    Bits[TotalWidth - 1 - Shift - I] = '1';
  return Bits;
}

// Two's-complement binary string of the format's smallest raw value (zero
// for unsigned formats), widened to TotalWidth and shifted left by Shift.
std::string minRawBits(const FXPFormat &F, unsigned TotalWidth,
                       unsigned Shift = 0) {
  std::string Bits(TotalWidth, '0');
  if (!F.IsSigned)
    return Bits;
  // min = -2^(Width-1) scaled by 2^Shift: sign-extended ones from bit
  // (Width-1)+Shift upward.
  for (unsigned I = F.Width - 1 + Shift; I < TotalWidth; ++I)
    Bits[TotalWidth - 1 - I] = '1';
  return Bits;
}

void requireFXP(const SMTExprRef &Exp) {
  fatalErrorIf(!Exp->Sort->isFXPSort(), "Expected fixed-point expression");
}

void requireFXPSort(const SMTSortRef &Sort) {
  fatalErrorIf(!Sort->isFXPSort(), "Expected fixed-point target sort");
}

// Extends a raw value by Extra bits, per the *source* format's signedness.
SMTExprRef extendRaw(SMTSolverImpl &S, const SMTExprRef &Raw, bool IsSigned,
                     unsigned Extra) {
  if (Extra == 0)
    return Raw;
  return IsSigned ? S.mkBVSignExt(Extra, Raw) : S.mkBVZeroExt(Extra, Raw);
}

// Aligns a fixed-point operand into format C as a plain-BV raw view,
// exactly: extend first (per the operand's own signedness), then shift the
// fraction point left. C must embed the operand's format, which
// commonFormat() guarantees.
SMTExprRef alignRaw(SMTSolverImpl &S, const SMTExprRef &Exp,
                    const FXPFormat &C) {
  FXPFormat F = formatOf(Exp->Sort);
  SMTExprRef Raw = S.mkFXPToRawBV(Exp);
  Raw = extendRaw(S, Raw, F.IsSigned, C.Width - F.Width);
  unsigned Shift = C.FracBits - F.FracBits;
  if (Shift != 0)
    Raw = S.mkBVShl(Raw, S.mkBVFromDec(Shift, C.Width));
  return Raw;
}

// Aligned raw operands plus their common format, shared by every binary op.
struct AlignedPair {
  FXPFormat Fmt;
  SMTExprRef LHS;
  SMTExprRef RHS;
};

AlignedPair alignPair(SMTSolverImpl &S, const SMTExprRef &LHS,
                      const SMTExprRef &RHS) {
  requireFXP(LHS);
  requireFXP(RHS);
  FXPFormat C = commonFormat(formatOf(LHS->Sort), formatOf(RHS->Sort));
  return AlignedPair{C, alignRaw(S, LHS, C), alignRaw(S, RHS, C)};
}

// Clamps a wide exact raw value to the format's range and narrows to the
// format width: the saturating counterpart of the truncating extracts in
// the non-saturating ops. Comparisons run at the wide width. SignedCmp
// selects signed comparisons (and enables the min-bound clamp); it must
// be true exactly when the wide view is sign-correct — signed operands,
// or unsigned values carried with a slack bit so no top bit is set.
// Unsigned views whose top bit can be set (the 2W product/quotient of
// unsigned operands) use unsigned comparisons, where only the max bound
// exists.
SMTExprRef clampRaw(SMTSolverImpl &S, const SMTExprRef &Wide, unsigned W,
                    const FXPFormat &F, bool SignedCmp) {
  SMTExprRef MaxW = S.mkBVFromBin(maxRawBits(F, W), W);
  SMTExprRef Over = SignedCmp ? S.mkBVSgt(Wide, MaxW) : S.mkBVUgt(Wide, MaxW);
  SMTExprRef Res = S.mkIte(Over, S.mkBVFromBin(maxRawBits(F, F.Width), F.Width),
                           S.mkBVExtract(F.Width - 1, 0, Wide));
  if (SignedCmp) {
    SMTExprRef MinW = S.mkBVFromBin(minRawBits(F, W), W);
    Res = S.mkIte(S.mkBVSlt(Wide, MinW),
                  S.mkBVFromBin(minRawBits(F, F.Width), F.Width), Res);
  }
  return Res;
}

// Adjusts a toward-zero signed quotient to floor: subtract one when the
// remainder is nonzero and the operand signs differ. Fixed-point division
// rounds down on inexact results (Clang/LLVM sdiv.fix, pinned by the
// execution oracle); bvsdiv rounds toward zero.
SMTExprRef floorAdjustQuotient(SMTSolverImpl &S, const SMTExprRef &Quot,
                               const SMTExprRef &L, const SMTExprRef &R,
                               unsigned W) {
  SMTExprRef RemNZ = S.mkNot(S.mkEqual(S.mkBVSRem(L, R), S.mkBVFromDec(0, W)));
  SMTExprRef SignsDiffer = S.mkNot(S.mkEqual(S.mkBVExtract(W - 1, W - 1, L),
                                             S.mkBVExtract(W - 1, W - 1, R)));
  return S.mkIte(S.mkAnd(RemNZ, SignsDiffer),
                 S.mkBVSub(Quot, S.mkBVFromDec(1, W)), Quot);
}

// Rounds a floored quotient under a rounding mode.
//
// Division cannot use shiftRounded: the discarded part is a remainder
// against an arbitrary divisor, not a fixed number of low bits, so the
// halfway test is 2*|rem| against |divisor| rather than a bit pattern.
// Quot must already be the floor (mkFXPDiv's floorAdjustQuotient), and L
// and R are the operands it came from, all at width W.
SMTExprRef roundQuotient(SMTSolverImpl &S, const SMTExprRef &Quot,
                         const SMTExprRef &L, const SMTExprRef &R, unsigned W,
                         bool Signed, FXPRM Mode) {
  if (Mode == FXPRM::TowardNegative)
    return Quot;
  SMTExprRef Zero = S.mkBVFromDec(0, W);
  SMTExprRef One = S.mkBVFromDec(1, W);
  // Remainder in the floor convention: L - Quot*R, which has the sign of
  // R and magnitude below |R|.
  SMTExprRef Rem = S.mkBVSub(L, S.mkBVMul(Quot, R));
  SMTExprRef Inexact = S.mkNot(S.mkEqual(Rem, Zero));
  auto absOf = [&](const SMTExprRef &V) {
    return Signed ? S.mkIte(S.mkBVSlt(V, Zero), S.mkBVNeg(V), V) : V;
  };
  // The quotient is negative when exactly one operand is.
  SMTExprRef Neg =
      Signed
          ? S.mkAnd(Inexact, S.mkNot(S.mkEqual(S.mkBVExtract(W - 1, W - 1, L),
                                               S.mkBVExtract(W - 1, W - 1, R))))
          : S.mkBool(false);

  switch (Mode) {
  case FXPRM::TowardPositive:
    return S.mkIte(Inexact, S.mkBVAdd(Quot, One), Quot);
  case FXPRM::TowardZero:
    return S.mkIte(S.mkAnd(Neg, Inexact), S.mkBVAdd(Quot, One), Quot);
  default:
    break;
  }
  // Nearest: compare twice the remainder against the divisor. Both are
  // taken as magnitudes, and the doubling needs one extra bit.
  SMTExprRef AR = S.mkBVZeroExt(1, absOf(Rem));
  SMTExprRef AD = S.mkBVZeroExt(1, absOf(R));
  SMTExprRef Twice = S.mkBVShl(AR, S.mkBVFromDec(1, W + 1));
  SMTExprRef Above = S.mkBVUgt(Twice, AD);
  SMTExprRef Tie = S.mkEqual(Twice, AD);
  SMTExprRef TieUp;
  switch (Mode) {
  case FXPRM::NearestTiesTowardPositive:
    TieUp = S.mkBool(true);
    break;
  case FXPRM::NearestTiesAwayFromZero:
    TieUp = S.mkNot(Neg);
    break;
  default: // ties to even
    TieUp = S.mkEqual(S.mkBVExtract(0, 0, Quot), S.mkBVFromDec(1, 1));
    break;
  }
  return S.mkIte(S.mkOr(Above, S.mkAnd(Tie, TieUp)), S.mkBVAdd(Quot, One),
                 Quot);
}

// Shifts Val right by Shift bits under a rounding mode, at Val's width.
//
// Every fixed-point operation that discards precision reduces to this:
// multiply drops the doubled fraction bits, narrowing drops the
// difference, fixed-to-integer drops all of them. Doing it in one place
// means the modes cannot drift apart between operations.
//
// The dropped bits decide the direction, so they are read before the
// shift; a caller that shifts first has already lost the information.
SMTExprRef shiftRounded(SMTSolverImpl &S, const SMTExprRef &Val, unsigned Shift,
                        unsigned W, bool Signed, FXPRM Mode) {
  if (Shift == 0)
    return Val;
  SMTExprRef Zero = S.mkBVFromDec(0, W);
  SMTExprRef Amount = S.mkBVFromDec(Shift, W);
  // Arithmetic shift for signed values: the quotient must floor, which is
  // what ashr does, and every mode is expressed as an adjustment from it.
  SMTExprRef Floor = Signed ? S.mkBVAshr(Val, Amount) : S.mkBVLshr(Val, Amount);
  SMTExprRef DropMask =
      S.mkBVFromBin(std::string(W - Shift, '0') + std::string(Shift, '1'), W);
  SMTExprRef Dropped = S.mkBVAnd(Val, DropMask);
  SMTExprRef Inexact = S.mkNot(S.mkEqual(Dropped, Zero));
  SMTExprRef One = S.mkBVFromDec(1, W);
  SMTExprRef Neg = Signed ? S.mkBVSlt(Val, Zero) : S.mkBool(false);

  switch (Mode) {
  case FXPRM::TowardNegative:
    return Floor;
  case FXPRM::TowardPositive:
    return S.mkIte(Inexact, S.mkBVAdd(Floor, One), Floor);
  case FXPRM::TowardZero:
    // Floor already truncates non-negative values; negatives need the
    // dropped part added back.
    return S.mkIte(S.mkAnd(Neg, Inexact), S.mkBVAdd(Floor, One), Floor);
  case FXPRM::NearestTiesTowardPositive:
  case FXPRM::NearestTiesAwayFromZero:
  case FXPRM::NearestTiesToEven:
    break;
  }
  // Nearest: compare the dropped part against half an ulp.
  SMTExprRef Half = S.mkBVFromBin(std::string(W - Shift, '0') + "1" +
                                      std::string(Shift ? Shift - 1 : 0, '0'),
                                  W);
  SMTExprRef Above = S.mkBVUgt(Dropped, Half);
  SMTExprRef Tie = S.mkEqual(Dropped, Half);
  SMTExprRef TieUp;
  switch (Mode) {
  case FXPRM::NearestTiesTowardPositive:
    TieUp = S.mkBool(true);
    break;
  case FXPRM::NearestTiesAwayFromZero:
    TieUp = S.mkNot(Neg);
    break;
  default: // NearestTiesToEven: up only when the kept bit is odd
    TieUp = S.mkEqual(S.mkBVExtract(0, 0, Floor), S.mkBVFromDec(1, 1));
    break;
  }
  return S.mkIte(S.mkOr(Above, S.mkAnd(Tie, TieUp)), S.mkBVAdd(Floor, One),
                 Floor);
}

} // namespace

// ---------------------------------------------------------------------------
// Sort and literals
// ---------------------------------------------------------------------------

SMTSortRef SMTSolverImpl::mkFXPSort(unsigned Width, unsigned FracBits,
                                    bool IsSigned) {
  fatalErrorIf(Width == 0, "Fixed-point width must be non-zero");
  fatalErrorIf(!IsSigned && FracBits > Width,
               "Unsigned fixed-point fraction cannot exceed the width");
  fatalErrorIf(IsSigned && FracBits >= Width,
               "Signed fixed-point needs a non-fraction sign bit");

  FXPSortCacheKey Key{Width, FracBits, IsSigned};
  auto It = FXPSortCache.find(Key);
  if (It != FXPSortCache.end())
    return It->second;

  SMTSortRef theSort = mkFXPSortImpl(Width, FracBits, IsSigned);
  assert(theSort->isFXPSort());
  FXPSortCache.emplace(Key, theSort);
  return theSort;
}

SMTExprRef SMTSolverImpl::mkFXPFromBin(const std::string &RawBits,
                                       const SMTSortRef &To) {
  requireFXPSort(To);
  fatalErrorIf(RawBits.size() != To->getWidth(),
               "Fixed-point literal width must match the sort width");
  return rewrapExprImpl(*mkBVFromBin(RawBits, To->getWidth()), To,
                        SMTExprKind::FXPConst);
}

SMTExprRef SMTSolverImpl::mkFXPFromRawBV(const SMTExprRef &Exp,
                                         const SMTSortRef &To) {
  fatalErrorIf(!Exp->Sort->isBVSort(), "Expected bit-vector expression");
  requireFXPSort(To);
  fatalErrorIf(Exp->getWidth() != To->getWidth(),
               "Bit-vector and fixed-point target widths must match");
  return rewrapExprImpl(*Exp, To, SMTExprKind::BVToFXP);
}

SMTExprRef SMTSolverImpl::mkFXPToRawBV(const SMTExprRef &Exp) {
  requireFXP(Exp);
  // Retag to a plain BV sort so downstream BV operations' same-sort checks
  // do not see a distinct FXP sort kind (the IEEEFPToBV precedent).
  return rewrapExprImpl(*Exp, mkBVSort(Exp->getWidth()),
                        SMTExprKind::FXPToRawBV);
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

SMTExprRef SMTSolverImpl::mkFXPAdd(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  return rewrapExprImpl(*mkBVAdd(P.LHS, P.RHS),
                        mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
                        SMTExprKind::FXPAdd);
}

SMTExprRef SMTSolverImpl::mkFXPSub(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  return rewrapExprImpl(*mkBVSub(P.LHS, P.RHS),
                        mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
                        SMTExprKind::FXPSub);
}

SMTExprRef SMTSolverImpl::mkFXPNeg(const SMTExprRef &Exp) {
  requireFXP(Exp);
  return rewrapExprImpl(*mkBVNeg(mkFXPToRawBV(Exp)), Exp->Sort,
                        SMTExprKind::FXPNeg);
}

SMTExprRef SMTSolverImpl::mkFXPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   FXPRM Mode) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // The exact product of two W-bit values fits in 2W bits; drop the extra
  // fraction bits of the raw product under Mode, then take the low W bits.
  // The dropped bits decide the rounding and are gone after the shift, so
  // no caller could recover this from a truncating result.
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef Prod = mkBVMul(L, R);
  Prod = shiftRounded(*this, Prod, P.Fmt.FracBits, 2 * P.Fmt.Width,
                      P.Fmt.IsSigned, Mode);
  return rewrapExprImpl(*mkBVExtract(P.Fmt.Width - 1, 0, Prod),
                        mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
                        SMTExprKind::FXPMul);
}

SMTExprRef SMTSolverImpl::mkFXPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   FXPRM Mode) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // (lhs * 2^N) / rhs at double width: extend first, then scale the
  // dividend — the shift cannot overflow 2W since N <= W.
  //
  // The quotient is computed as a floor and then adjusted to Mode.
  // FXPRM::TowardNegative reproduces C: TR 18037 leaves the direction
  // implementation-defined and Clang floors (LLVM sdiv.fix), pinned by
  // the execution oracle (scripts/fxp_oracle_gen.py) — the
  // C-integer-division analogy does not govern fixed-point.
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  if (P.Fmt.FracBits != 0)
    L = mkBVShl(L, mkBVFromDec(P.Fmt.FracBits, 2 * P.Fmt.Width));
  SMTExprRef Quot = P.Fmt.IsSigned ? mkBVSDiv(L, R) : mkBVUDiv(L, R);
  if (P.Fmt.IsSigned)
    Quot = floorAdjustQuotient(*this, Quot, L, R, 2 * P.Fmt.Width);
  Quot =
      roundQuotient(*this, Quot, L, R, 2 * P.Fmt.Width, P.Fmt.IsSigned, Mode);
  return rewrapExprImpl(*mkBVExtract(P.Fmt.Width - 1, 0, Quot),
                        mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
                        SMTExprKind::FXPDiv);
}

SMTExprRef SMTSolverImpl::mkFXPShl(const SMTExprRef &Exp, unsigned Amount) {
  requireFXP(Exp);
  fatalErrorIf(Amount >= Exp->getWidth(),
               "Fixed-point shift amount must be smaller than the width");
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  return rewrapExprImpl(*mkBVShl(Raw, mkBVFromDec(Amount, Exp->getWidth())),
                        Exp->Sort, SMTExprKind::FXPShl);
}

SMTExprRef SMTSolverImpl::mkFXPShr(const SMTExprRef &Exp, unsigned Amount) {
  requireFXP(Exp);
  fatalErrorIf(Amount >= Exp->getWidth(),
               "Fixed-point shift amount must be smaller than the width");
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef AmountExp = mkBVFromDec(Amount, Exp->getWidth());
  SMTExprRef Shifted = Exp->Sort->isFXPSignedSort() ? mkBVAshr(Raw, AmountExp)
                                                    : mkBVLshr(Raw, AmountExp);
  return rewrapExprImpl(*Shifted, Exp->Sort, SMTExprKind::FXPShr);
}

// ---------------------------------------------------------------------------
// Saturating arithmetic (TR 18037 `_Sat`)
//
// Each variant computes the exact result in a wide intermediate and clamps
// with clampRaw. Clamping the post-truncation value is output-equivalent to
// clamping the exact result: on the max side the two differ only when the
// exact value lies in (max, max+1ulp), where truncation already lands on
// max; the min side is identical (floor/toward-zero cannot cross min from
// above). Saturating overflow is defined behavior, so there are no paired
// predicates; mkFXPDivSat still pairs with mkFXPDivByZero.
// ---------------------------------------------------------------------------

SMTExprRef SMTSolverImpl::mkFXPAddSat(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // Two extra bits hold the exact sum sign-correctly for both
  // signednesses: one for the carry, one so the unsigned sum's top bit
  // never lands in the sign position.
  SMTExprRef Sum = mkBVAdd(extendRaw(*this, P.LHS, P.Fmt.IsSigned, 2),
                           extendRaw(*this, P.RHS, P.Fmt.IsSigned, 2));
  return rewrapExprImpl(*clampRaw(*this, Sum, P.Fmt.Width + 2, P.Fmt,
                                  /*SignedCmp=*/true),
                        mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
                        SMTExprKind::FXPAddSat);
}

SMTExprRef SMTSolverImpl::mkFXPSubSat(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // Two extra bits keep the exact difference sign-correct for both
  // signednesses; an unsigned underflow then clamps against min = 0.
  SMTExprRef Diff = mkBVSub(extendRaw(*this, P.LHS, P.Fmt.IsSigned, 2),
                            extendRaw(*this, P.RHS, P.Fmt.IsSigned, 2));
  return rewrapExprImpl(*clampRaw(*this, Diff, P.Fmt.Width + 2, P.Fmt,
                                  /*SignedCmp=*/true),
                        mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
                        SMTExprKind::FXPSubSat);
}

SMTExprRef SMTSolverImpl::mkFXPNegSat(const SMTExprRef &Exp) {
  requireFXP(Exp);
  FXPFormat F = formatOf(Exp->Sort);
  SMTExprRef Neg = mkBVNeg(extendRaw(*this, mkFXPToRawBV(Exp), F.IsSigned, 2));
  return rewrapExprImpl(*clampRaw(*this, Neg, F.Width + 2, F,
                                  /*SignedCmp=*/true),
                        Exp->Sort, SMTExprKind::FXPNegSat);
}

SMTExprRef SMTSolverImpl::mkFXPMulSat(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // Same 2W exact product and floor shift as mkFXPMul; clamp instead of
  // truncating. Unsigned products can set the top bit at 2W, so the
  // comparisons follow the format signedness (mirroring the overflow
  // predicate).
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef Prod = mkBVMul(L, R);
  if (P.Fmt.FracBits != 0) {
    SMTExprRef Amount = mkBVFromDec(P.Fmt.FracBits, 2 * P.Fmt.Width);
    Prod = P.Fmt.IsSigned ? mkBVAshr(Prod, Amount) : mkBVLshr(Prod, Amount);
  }
  return rewrapExprImpl(
      *clampRaw(*this, Prod, 2 * P.Fmt.Width, P.Fmt, P.Fmt.IsSigned),
      mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
      SMTExprKind::FXPMulSat);
}

SMTExprRef SMTSolverImpl::mkFXPDivSat(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // Same 2W scaled dividend and floored quotient as mkFXPDiv; clamp
  // instead of truncating. The signed min/-1 case lands above max at 2W
  // and clamps there. The value is meaningful only under !mkFXPDivByZero.
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  if (P.Fmt.FracBits != 0)
    L = mkBVShl(L, mkBVFromDec(P.Fmt.FracBits, 2 * P.Fmt.Width));
  SMTExprRef Quot = P.Fmt.IsSigned ? mkBVSDiv(L, R) : mkBVUDiv(L, R);
  if (P.Fmt.IsSigned)
    Quot = floorAdjustQuotient(*this, Quot, L, R, 2 * P.Fmt.Width);
  return rewrapExprImpl(
      *clampRaw(*this, Quot, 2 * P.Fmt.Width, P.Fmt, P.Fmt.IsSigned),
      mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
      SMTExprKind::FXPDivSat);
}

SMTExprRef SMTSolverImpl::mkFXPShlSat(const SMTExprRef &Exp, unsigned Amount) {
  requireFXP(Exp);
  unsigned W = Exp->getWidth();
  fatalErrorIf(Amount >= W,
               "Fixed-point shift amount must be smaller than the width");
  FXPFormat F = formatOf(Exp->Sort);
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef Shifted = mkBVShl(Raw, mkBVFromDec(Amount, W));
  SMTExprRef Ovf = mkFXPShlOverflow(Exp, Amount);
  SMTExprRef Max = mkBVFromBin(maxRawBits(F, F.Width), F.Width);
  SMTExprRef Clamped;
  if (!F.IsSigned) {
    Clamped = mkIte(Ovf, Max, Shifted);
  } else {
    // The clamp direction follows the operand's sign: a negative value
    // that overflows saturates to min, a positive one to max.
    SMTExprRef Neg = mkEqual(mkBVExtract(W - 1, W - 1, Raw), mkBVFromDec(1, 1));
    SMTExprRef Min = mkBVFromBin(minRawBits(F, F.Width), F.Width);
    Clamped = mkIte(Ovf, mkIte(Neg, Min, Max), Shifted);
  }
  return rewrapExprImpl(*Clamped, Exp->Sort, SMTExprKind::FXPShlSat);
}

// Runtime-amount shifts. The overflow test is the round-trip identity:
// shifting back recovers the operand exactly when nothing significant
// (including the sign) was discarded — equivalent to the constant
// version's top-bits check for every Amount < Width.

namespace {

void requireShiftAmount(const SMTExprRef &Exp, const SMTExprRef &Amount) {
  fatalErrorIf(!Amount->Sort->isBVSort(), "Expected bit-vector shift amount");
  fatalErrorIf(Amount->getWidth() != Exp->getWidth(),
               "Shift amount width must match the operand width");
}

} // namespace

SMTExprRef SMTSolverImpl::mkFXPShlExpr(const SMTExprRef &Exp,
                                       const SMTExprRef &Amount) {
  requireFXP(Exp);
  requireShiftAmount(Exp, Amount);
  return rewrapExprImpl(*mkBVShl(mkFXPToRawBV(Exp), Amount), Exp->Sort,
                        SMTExprKind::FXPShl);
}

SMTExprRef SMTSolverImpl::mkFXPShrExpr(const SMTExprRef &Exp,
                                       const SMTExprRef &Amount) {
  requireFXP(Exp);
  requireShiftAmount(Exp, Amount);
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef Shifted = Exp->Sort->isFXPSignedSort() ? mkBVAshr(Raw, Amount)
                                                    : mkBVLshr(Raw, Amount);
  return rewrapExprImpl(*Shifted, Exp->Sort, SMTExprKind::FXPShr);
}

SMTExprRef SMTSolverImpl::mkFXPShlOverflowExpr(const SMTExprRef &Exp,
                                               const SMTExprRef &Amount) {
  requireFXP(Exp);
  requireShiftAmount(Exp, Amount);
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef Shifted = mkBVShl(Raw, Amount);
  SMTExprRef Back = Exp->Sort->isFXPSignedSort() ? mkBVAshr(Shifted, Amount)
                                                 : mkBVLshr(Shifted, Amount);
  return mkNot(mkEqual(Back, Raw));
}

SMTExprRef SMTSolverImpl::mkFXPShlSatExpr(const SMTExprRef &Exp,
                                          const SMTExprRef &Amount) {
  requireFXP(Exp);
  requireShiftAmount(Exp, Amount);
  FXPFormat F = formatOf(Exp->Sort);
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef Shifted = mkBVShl(Raw, Amount);
  SMTExprRef Ovf = mkFXPShlOverflowExpr(Exp, Amount);
  SMTExprRef Max = mkBVFromBin(maxRawBits(F, F.Width), F.Width);
  SMTExprRef Clamped;
  if (!F.IsSigned) {
    Clamped = mkIte(Ovf, Max, Shifted);
  } else {
    SMTExprRef Neg =
        mkEqual(mkBVExtract(F.Width - 1, F.Width - 1, Raw), mkBVFromDec(1, 1));
    SMTExprRef Min = mkBVFromBin(minRawBits(F, F.Width), F.Width);
    Clamped = mkIte(Ovf, mkIte(Neg, Min, Max), Shifted);
  }
  return rewrapExprImpl(*Clamped, Exp->Sort, SMTExprKind::FXPShlSat);
}

// ---------------------------------------------------------------------------
// Comparisons
// ---------------------------------------------------------------------------

SMTExprRef SMTSolverImpl::mkFXPLt(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  return P.Fmt.IsSigned ? mkBVSlt(P.LHS, P.RHS) : mkBVUlt(P.LHS, P.RHS);
}

SMTExprRef SMTSolverImpl::mkFXPLe(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  return P.Fmt.IsSigned ? mkBVSle(P.LHS, P.RHS) : mkBVUle(P.LHS, P.RHS);
}

SMTExprRef SMTSolverImpl::mkFXPGt(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return mkFXPLt(RHS, LHS);
}

SMTExprRef SMTSolverImpl::mkFXPGe(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return mkFXPLe(RHS, LHS);
}

SMTExprRef SMTSolverImpl::mkFXPEqual(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  return mkEqual(P.LHS, P.RHS);
}

// ---------------------------------------------------------------------------
// UB predicates
// ---------------------------------------------------------------------------

SMTExprRef SMTSolverImpl::mkFXPAddOverflow(const SMTExprRef &LHS,
                                           const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // Same width, same two's-complement semantics: the BV predicate on the
  // aligned raws is exactly fixed-point add overflow.
  return P.Fmt.IsSigned ? mkBVSAddOverflow(P.LHS, P.RHS)
                        : mkBVUAddOverflow(P.LHS, P.RHS);
}

SMTExprRef SMTSolverImpl::mkFXPSubOverflow(const SMTExprRef &LHS,
                                           const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  return P.Fmt.IsSigned ? mkBVSSubOverflow(P.LHS, P.RHS)
                        : mkBVUSubOverflow(P.LHS, P.RHS);
}

SMTExprRef SMTSolverImpl::mkFXPNegOverflow(const SMTExprRef &Exp) {
  requireFXP(Exp);
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  // Unsigned negation of any non-zero value leaves [0, max]; the BV
  // predicate only knows the signed-minimum case.
  if (!Exp->Sort->isFXPSignedSort())
    return mkNot(mkEqual(Raw, mkBVFromDec(0, Exp->getWidth())));
  return mkBVNegOverflow(Raw);
}

SMTExprRef SMTSolverImpl::mkFXPMulOverflow(const SMTExprRef &LHS,
                                           const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  unsigned W2 = 2 * P.Fmt.Width;
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef Prod = mkBVMul(L, R);
  // Test the raw (pre-rounding) product against the format bounds scaled by
  // 2^N. The scaled bounds fit at 2W: max*2^N < 2^(W+N) <= 2^2W unsigned,
  // and < 2^(2W-1) signed since N <= W-1 there.
  SMTExprRef Max = mkBVFromBin(maxRawBits(P.Fmt, W2, P.Fmt.FracBits), W2);
  if (!P.Fmt.IsSigned)
    return mkBVUgt(Prod, Max);
  SMTExprRef Min = mkBVFromBin(minRawBits(P.Fmt, W2, P.Fmt.FracBits), W2);
  return mkOr(mkBVSgt(Prod, Max), mkBVSlt(Prod, Min));
}

SMTExprRef SMTSolverImpl::mkFXPDivByZero(const SMTExprRef &RHS) {
  requireFXP(RHS);
  return mkEqual(mkFXPToRawBV(RHS), mkBVFromDec(0, RHS->getWidth()));
}

SMTExprRef SMTSolverImpl::mkFXPDivOverflow(const SMTExprRef &LHS,
                                           const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  unsigned W2 = 2 * P.Fmt.Width;
  // The exact quotient q = (lhs * 2^N) / rhs must lie in [min, max].
  // Multiply the bounds through by rhs (sign-aware) instead of dividing:
  // with Num = lhs * 2^N and Den = rhs at double width,
  //   q > max  iff  Den > 0 ? Num > max*Den : Num < max*Den
  // and symmetrically for min. All products fit at 2W:
  // |max*Den| <= 2^(W-1) * 2^(W-1) < 2^(2W-1), and |Num| <= 2^(2W-2) for
  // signed formats (N <= W-1); the unsigned case uses unsigned compares
  // where everything is below 2^2W. False when the divisor is zero —
  // that is mkFXPDivByZero's report, not this one's.
  SMTExprRef Num = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef Den = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  if (P.Fmt.FracBits != 0)
    Num = mkBVShl(Num, mkBVFromDec(P.Fmt.FracBits, W2));
  SMTExprRef NotZero = mkNot(mkEqual(Den, mkBVFromDec(0, W2)));

  SMTExprRef Max = mkBVFromBin(maxRawBits(P.Fmt, W2), W2);
  SMTExprRef MaxD = mkBVMul(Max, Den);
  if (!P.Fmt.IsSigned) {
    // Unsigned: min is zero and the quotient is non-negative; only the max
    // bound can be exceeded.
    return mkAnd(NotZero, mkBVUgt(Num, MaxD));
  }
  SMTExprRef Min = mkBVFromBin(minRawBits(P.Fmt, W2), W2);
  SMTExprRef MinD = mkBVMul(Min, Den);
  SMTExprRef DenPos = mkBVSgt(Den, mkBVFromDec(0, W2));
  SMTExprRef AboveMax = mkIte(DenPos, mkBVSgt(Num, MaxD), mkBVSlt(Num, MaxD));
  SMTExprRef BelowMin = mkIte(DenPos, mkBVSlt(Num, MinD), mkBVSgt(Num, MinD));
  return mkAnd(NotZero, mkOr(AboveMax, BelowMin));
}

SMTExprRef SMTSolverImpl::mkFXPShlOverflow(const SMTExprRef &Exp,
                                           unsigned Amount) {
  requireFXP(Exp);
  unsigned W = Exp->getWidth();
  fatalErrorIf(Amount >= W,
               "Fixed-point shift amount must be smaller than the width");
  if (Amount == 0)
    return mkBool(false);
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  if (!Exp->Sort->isFXPSignedSort()) {
    // Overflow iff any shifted-out bit is set.
    SMTExprRef Top = mkBVExtract(W - 1, W - Amount, Raw);
    return mkNot(mkEqual(Top, mkBVFromDec(0, Amount)));
  }
  // Signed: the shifted-out bits plus the resulting sign bit must all equal
  // the original sign, i.e. be all-zeros or all-ones.
  SMTExprRef Top = mkBVExtract(W - 1, W - Amount - 1, Raw);
  SMTExprRef Zeros = mkBVFromDec(0, Amount + 1);
  SMTExprRef Ones = mkBVNot(Zeros);
  return mkNot(mkOr(mkEqual(Top, Zeros), mkEqual(Top, Ones)));
}

// ---------------------------------------------------------------------------
// Conversions
// ---------------------------------------------------------------------------

namespace {

// Shared by mkFXPToFXP and its overflow predicate: the source raw view in a
// wide intermediate, extended (per source signedness) with enough headroom
// that neither the value's fraction-alignment shift nor the bound scaling in
// the overflow predicate can lose bits, plus a slack bit so signed
// comparisons on the wide value are exact even for unsigned sources.
std::pair<SMTExprRef, unsigned> wideForConversion(SMTSolverImpl &S,
                                                  const SMTExprRef &Exp,
                                                  const FXPFormat &To) {
  FXPFormat From = formatOf(Exp->Sort);
  unsigned GrowUp = To.FracBits > From.FracBits ? To.FracBits - From.FracBits
                                                : 0; // value shifts left
  unsigned GrowDown = From.FracBits > To.FracBits ? From.FracBits - To.FracBits
                                                  : 0; // bounds shift left
  unsigned Wide = std::max(From.Width, To.Width) + GrowUp + GrowDown + 1;
  SMTExprRef Raw = S.mkFXPToRawBV(Exp);
  return {extendRaw(S, Raw, From.IsSigned, Wide - From.Width), Wide};
}

} // namespace

SMTExprRef SMTSolverImpl::mkFXPToFXP(const SMTExprRef &Exp,
                                     const SMTSortRef &To) {
  requireFXP(Exp);
  requireFXPSort(To);
  FXPFormat From = formatOf(Exp->Sort);
  FXPFormat Target = formatOf(To);
  auto [Raw, Wide] = wideForConversion(*this, Exp, Target);
  if (Target.FracBits > From.FracBits) {
    Raw = mkBVShl(Raw, mkBVFromDec(Target.FracBits - From.FracBits, Wide));
  } else if (From.FracBits > Target.FracBits) {
    // Narrowing the fraction truncates low bits (floor).
    SMTExprRef Amount = mkBVFromDec(From.FracBits - Target.FracBits, Wide);
    Raw = From.IsSigned ? mkBVAshr(Raw, Amount) : mkBVLshr(Raw, Amount);
  }
  return rewrapExprImpl(*mkBVExtract(Target.Width - 1, 0, Raw), To,
                        SMTExprKind::FXPToFXP);
}

SMTExprRef SMTSolverImpl::mkFXPToFXPOverflow(const SMTExprRef &Exp,
                                             const SMTSortRef &To) {
  requireFXP(Exp);
  requireFXPSort(To);
  FXPFormat From = formatOf(Exp->Sort);
  FXPFormat Target = formatOf(To);
  auto [Raw, Wide] = wideForConversion(*this, Exp, Target);
  // Compare the exact (pre-rounding) value: bring value and bounds to the
  // *larger* fraction scale of the two formats so no fraction bit is
  // dropped before the check; Wide has headroom for both shifts.
  unsigned Scale = std::max(From.FracBits, Target.FracBits);
  if (Scale > From.FracBits)
    Raw = mkBVShl(Raw, mkBVFromDec(Scale - From.FracBits, Wide));
  unsigned BoundShift = Scale - Target.FracBits;
  // The wide value is sign-correct thanks to the slack bit, so signed
  // comparisons are exact for both signednesses of the source.
  SMTExprRef Max = mkBVFromBin(maxRawBits(Target, Wide, BoundShift), Wide);
  SMTExprRef Min = mkBVFromBin(minRawBits(Target, Wide, BoundShift), Wide);
  return mkOr(mkBVSgt(Raw, Max), mkBVSlt(Raw, Min));
}

SMTExprRef SMTSolverImpl::mkFXPToFXPSat(const SMTExprRef &Exp,
                                        const SMTSortRef &To) {
  requireFXP(Exp);
  requireFXPSort(To);
  FXPFormat From = formatOf(Exp->Sort);
  FXPFormat Target = formatOf(To);
  // Same wide intermediate and fraction shifts as mkFXPToFXP (floor on
  // narrowing), clamped instead of truncated. Wide's slack bit keeps the
  // view sign-correct for both source signednesses, so the comparisons
  // are signed (the overflow predicate's argument).
  auto [Raw, Wide] = wideForConversion(*this, Exp, Target);
  if (Target.FracBits > From.FracBits) {
    Raw = mkBVShl(Raw, mkBVFromDec(Target.FracBits - From.FracBits, Wide));
  } else if (From.FracBits > Target.FracBits) {
    SMTExprRef Amount = mkBVFromDec(From.FracBits - Target.FracBits, Wide);
    Raw = From.IsSigned ? mkBVAshr(Raw, Amount) : mkBVLshr(Raw, Amount);
  }
  return rewrapExprImpl(*clampRaw(*this, Raw, Wide, Target,
                                  /*SignedCmp=*/true),
                        To, SMTExprKind::FXPToFXPSat);
}

SMTExprRef SMTSolverImpl::mkFXPFromBV(const SMTExprRef &Exp, bool SrcSigned,
                                      const SMTSortRef &To) {
  fatalErrorIf(!Exp->Sort->isBVSort(), "Expected bit-vector expression");
  requireFXPSort(To);
  // An integer is a fixed-point value with zero fraction bits; converting
  // is then a format conversion from (width, 0, source signedness) — the
  // source type's signedness fixes the value, the target format only the
  // representation. Overflow of this conversion is queryable through
  // mkFXPToFXPOverflow on the same reinterpretation.
  SMTSortRef IntSort = mkFXPSort(Exp->getWidth(), 0, SrcSigned);
  return mkFXPToFXP(mkFXPFromRawBV(Exp, IntSort), To);
}

SMTExprRef SMTSolverImpl::mkFXPToBV(const SMTExprRef &Exp, unsigned ToWidth) {
  requireFXP(Exp);
  fatalErrorIf(ToWidth == 0, "Target width must be non-zero");
  FXPFormat From = formatOf(Exp->Sort);
  // Round toward zero — the direction TR 18037 specifies for fixed-point to
  // integer conversion. A plain arithmetic shift would floor (-1.5 -> -2);
  // signed division by 2^N truncates toward zero (-1.5 -> -1). The target
  // integer's signedness follows the source format's.
  unsigned Wide = std::max(From.Width, ToWidth + From.FracBits) + 1;
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  Raw = extendRaw(*this, Raw, From.IsSigned, Wide - From.Width);
  if (From.FracBits != 0) {
    std::string PowBits(Wide, '0');
    PowBits[Wide - 1 - From.FracBits] = '1';
    SMTExprRef Pow = mkBVFromBin(PowBits, Wide);
    Raw = From.IsSigned ? mkBVSDiv(Raw, Pow) : mkBVUDiv(Raw, Pow);
  }
  return rewrapExprImpl(*mkBVExtract(ToWidth - 1, 0, Raw), mkBVSort(ToWidth),
                        SMTExprKind::FXPToBV);
}

SMTExprRef SMTSolverImpl::mkFXPToBVOverflow(const SMTExprRef &Exp,
                                            unsigned ToWidth, bool ToSigned) {
  requireFXP(Exp);
  fatalErrorIf(ToWidth == 0, "Target width must be non-zero");
  FXPFormat From = formatOf(Exp->Sort);
  // C converts to integer by taking the toward-zero integral part first;
  // it is UB iff *that* does not fit the target. So unlike the mul/div and
  // fixed-to-fixed predicates, this one checks the rounded quotient.
  unsigned Wide = std::max(From.Width, ToWidth + From.FracBits) + 1;
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  Raw = extendRaw(*this, Raw, From.IsSigned, Wide - From.Width);
  if (From.FracBits != 0) {
    std::string PowBits(Wide, '0');
    PowBits[Wide - 1 - From.FracBits] = '1';
    SMTExprRef Pow = mkBVFromBin(PowBits, Wide);
    Raw = From.IsSigned ? mkBVSDiv(Raw, Pow) : mkBVUDiv(Raw, Pow);
  }
  FXPFormat IntTarget{ToWidth, 0, ToSigned};
  SMTExprRef Max = mkBVFromBin(maxRawBits(IntTarget, Wide), Wide);
  SMTExprRef Min = mkBVFromBin(minRawBits(IntTarget, Wide), Wide);
  return mkOr(mkBVSgt(Raw, Max), mkBVSlt(Raw, Min));
}

SMTExprRef SMTSolverImpl::mkFXPToBVSat(const SMTExprRef &Exp, unsigned ToWidth,
                                       bool ToSigned) {
  requireFXP(Exp);
  fatalErrorIf(ToWidth == 0, "Target width must be non-zero");
  FXPFormat From = formatOf(Exp->Sort);
  // Same toward-zero rounding as mkFXPToBV (signed division by 2^N),
  // clamped to the integer target's range instead of truncated. Wide's
  // slack bit keeps the comparisons sign-correct for both signednesses.
  unsigned Wide = std::max(From.Width, ToWidth + From.FracBits) + 1;
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  Raw = extendRaw(*this, Raw, From.IsSigned, Wide - From.Width);
  if (From.FracBits != 0) {
    std::string PowBits(Wide, '0');
    PowBits[Wide - 1 - From.FracBits] = '1';
    SMTExprRef Pow = mkBVFromBin(PowBits, Wide);
    Raw = From.IsSigned ? mkBVSDiv(Raw, Pow) : mkBVUDiv(Raw, Pow);
  }
  FXPFormat IntTarget{ToWidth, 0, ToSigned};
  return rewrapExprImpl(*clampRaw(*this, Raw, Wide, IntTarget,
                                  /*SignedCmp=*/true),
                        mkBVSort(ToWidth), SMTExprKind::FXPToBVSat);
}

// ---------------------------------------------------------------------------
// Rounding to a fraction width (TR 18037 roundfx)
// ---------------------------------------------------------------------------

SMTExprRef SMTSolverImpl::mkFXPRound(const SMTExprRef &Exp, unsigned Digits,
                                     FXPRM Tie) {
  requireFXP(Exp);
  FXPFormat F = formatOf(Exp->Sort);
  // Keeping at least every fraction bit is the identity; libc clamps a
  // negative count to zero, which is unrepresentable in an unsigned
  // parameter and so cannot occur here.
  if (Digits >= F.FracBits)
    return Exp;
  // Round to nearest by adding a bias and then clearing the bits below
  // the kept precision. Half an ulp biases ties upward; subtracting one
  // from it on negative inputs turns that into ties away from zero, and
  // adding the lowest kept bit instead turns it into ties to even. The
  // bias can carry past the format's maximum, which saturates to MAX
  // instead of wrapping — so the sum is computed one bit wider and
  // compared there, where it is exact for both signednesses.
  unsigned Shift = F.FracBits - Digits;
  unsigned W = F.Width + 1;
  SMTExprRef Raw = extendRaw(*this, mkFXPToRawBV(Exp), F.IsSigned, 1);
  std::string HalfBits(W, '0');
  HalfBits[W - Shift] = '1'; // 2^(Shift-1), half an ulp of the result
  SMTExprRef Bias = mkBVFromBin(HalfBits, W);
  SMTExprRef One = mkBVFromDec(1, W);
  SMTExprRef Zero = mkBVFromDec(0, W);
  // Every mode is the same mask with a different bias. The nearest modes
  // start from half an ulp and adjust; the directed modes never consult
  // the halfway point at all.
  SMTExprRef DroppedMask =
      mkBVFromBin(std::string(W - Shift, '0') + std::string(Shift, '1'), W);
  SMTExprRef HasDropped = mkNot(mkEqual(mkBVAnd(Raw, DroppedMask), Zero));
  switch (Tie) {
  case FXPRM::NearestTiesTowardPositive:
    break;
  case FXPRM::NearestTiesAwayFromZero:
    // Only signed formats have negative values to bias differently.
    if (F.IsSigned)
      Bias = mkBVSub(Bias, mkIte(mkBVSlt(Raw, Zero), One, Zero));
    break;
  case FXPRM::NearestTiesToEven:
    // half - 1 + (lowest kept bit): a tie lands on the even neighbour.
    Bias = mkBVAdd(mkBVSub(Bias, One),
                   mkBVZeroExt(W - 1, mkBVExtract(Shift, Shift, Raw)));
    break;
  case FXPRM::TowardNegative:
    // Masking alone floors, for both signednesses.
    Bias = Zero;
    break;
  case FXPRM::TowardZero:
    // Floor for non-negative values; for negatives, floor is one ulp too
    // low whenever bits were actually dropped, so add them back.
    Bias = F.IsSigned
               ? mkIte(mkAnd(mkBVSlt(Raw, Zero), HasDropped), DroppedMask, Zero)
               : Zero;
    break;
  case FXPRM::TowardPositive:
    // Ceiling: masking floors, so push up by the dropped bits when any
    // were nonzero.
    Bias = mkIte(HasDropped, DroppedMask, Zero);
    break;
  }
  SMTExprRef Sum = mkBVAdd(Raw, Bias);
  std::string MaskBits(W, '1');
  MaskBits.replace(W - Shift, Shift, Shift, '0');
  SMTExprRef Rounded = mkBVAnd(Sum, mkBVFromBin(MaskBits, W));
  SMTExprRef Max = mkBVFromBin(maxRawBits(F, W), W);
  // Overflow is exactly "the biased sum exceeds MAX". The slack bit keeps
  // the sum exact for both signednesses, but the comparison must follow
  // the format's own signedness: an unsigned format's MAX is all-ones in
  // F.Width bits, which a signed compare would read as negative once the
  // format fills the widened value.
  SMTExprRef Res =
      mkIte(F.IsSigned ? mkBVSgt(Sum, Max) : mkBVUgt(Sum, Max), Max, Rounded);
  return rewrapExprImpl(*mkBVExtract(F.Width - 1, 0, Res), Exp->Sort,
                        SMTExprKind::FXPRound);
}

SMTExprRef SMTSolverImpl::mkFXPAbs(const SMTExprRef &Exp) {
  requireFXP(Exp);
  FXPFormat F = formatOf(Exp->Sort);
  if (!F.IsSigned)
    return Exp;
  // Saturating: the most negative value negates to itself in two's
  // complement, so it maps to MAX instead of wrapping (LLVM libc's
  // choice, and the only total one).
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef Min = mkBVFromBin(minRawBits(F, F.Width), F.Width);
  SMTExprRef Res =
      mkIte(mkEqual(Raw, Min), mkBVFromBin(maxRawBits(F, F.Width), F.Width),
            mkIte(mkBVSlt(Raw, mkBVFromDec(0, F.Width)), mkBVNeg(Raw), Raw));
  return rewrapExprImpl(*Res, Exp->Sort, SMTExprKind::FXPAbs);
}

SMTExprRef SMTSolverImpl::mkFXPCountls(const SMTExprRef &Exp,
                                       unsigned ToWidth) {
  requireFXP(Exp);
  fatalErrorIf(ToWidth == 0, "Target width must be non-zero");
  FXPFormat F = formatOf(Exp->Sort);
  // The largest possible count is every counted bit being a sign copy;
  // a narrower target would silently truncate that to a wrong answer.
  fatalErrorIf(ToWidth < 64 && (F.IsSigned ? F.Width - 1 : F.Width) >
                                   (uint64_t(1) << ToWidth) - 1,
               "Target width is too narrow to hold the leading-sign count");
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  // Complementing a negative value turns leading ones into leading
  // zeros, so both signs reduce to counting leading zeros; the sign bit
  // itself is not redundant and is excluded from the count.
  if (F.IsSigned)
    Raw = mkIte(mkBVSlt(Raw, mkBVFromDec(0, F.Width)), mkBVNot(Raw), Raw);
  unsigned Counted = F.IsSigned ? F.Width - 1 : F.Width;
  SMTExprRef Payload = mkBVExtract(Counted - 1, 0, Raw);
  // Binary search rather than a linear chain of per-bit tests — the shape
  // the FP leading-zero encoder uses (#127), which measured far better on
  // hard instances. The payload is left-aligned in a power-of-two window
  // whose low padding bits are ones, so each step is a plain "is the
  // upper half zero?" test with no width bookkeeping: the padding can
  // never be mistaken for a leading zero.
  unsigned P = 1;
  while (P < Counted)
    P *= 2;
  SMTExprRef Rest = mkBVZeroExt(P - Counted, Payload);
  if (P != Counted) {
    Rest = mkBVShl(Rest, mkBVFromDec(P - Counted, P));
    Rest = mkBVOr(Rest, mkBVFromBin(std::string(Counted, '0') +
                                        std::string(P - Counted, '1'),
                                    P));
  }
  SMTExprRef Count = mkBVFromDec(0, ToWidth);
  for (unsigned Step = P / 2; Step != 0; Step /= 2) {
    SMTExprRef Top = mkBVExtract(P - 1, P - Step, Rest);
    SMTExprRef AllZero = mkEqual(Top, mkBVFromDec(0, Step));
    Count = mkBVAdd(Count, mkIte(AllZero, mkBVFromDec(Step, ToWidth),
                                 mkBVFromDec(0, ToWidth)));
    Rest = mkIte(AllZero, mkBVShl(Rest, mkBVFromDec(Step, P)), Rest);
  }
  // An all-zero payload has every counted bit a sign copy; the padded
  // search cannot reach that count, so it is selected directly.
  SMTExprRef AllSign = mkEqual(Payload, mkBVFromDec(0, Counted));
  Count = mkIte(AllSign, mkBVFromDec(Counted, ToWidth), Count);
  return rewrapExprImpl(*Count, mkBVSort(ToWidth), SMTExprKind::FXPCountls);
}

namespace {

// Formats mkFXPExp supports: the C _Accum types whose hardest-to-round
// input has been measured exhaustively (scripts/fxp_exp_bounds.txt).
// Width, FracBits, IsSigned, and the fractional bits an intermediate
// needs for the final rounding to be decidable everywhere.
struct ExpFormatBound {
  unsigned Width, FracBits;
  bool IsSigned;
  unsigned RoundingBits;
};

constexpr ExpFormatBound ExpBounds[] = {
    {16, 7, true, 19},   {16, 8, false, 23}, {32, 15, true, 37},
    {32, 16, false, 37}, {64, 31, true, 68}, {64, 32, false, 75},
};

const ExpFormatBound *findExpBound(const FXPFormat &F) {
  for (const ExpFormatBound &B : ExpBounds)
    if (B.Width == F.Width && B.FracBits == F.FracBits &&
        B.IsSigned == F.IsSigned)
      return &B;
  return nullptr;
}

// Extra fractional bits carried beyond what the rounding needs. The
// series below truncates at every division, and those losses compound
// faster than the remainder bound alone suggests: a model of this
// encoding in exact integer arithmetic still mis-rounded a handful of
// inputs with 8 spare bits and needed 12 (u8.8) and 16 (s16.15) to come
// clean, so the margin is set well above the observed trend. Bit-vector
// width is cheap here.
constexpr unsigned ExpGuardBits = 32;

// floor(ln2 * 2^Prec) as a Width-bit binary string, computed exactly from
// ln2 = sum_{k>=1} 1/(k*2^k). The series is truncated where its terms fall
// below the last bit kept, so the result is exact for any Prec; deriving
// it here rather than hard-coding digits keeps the constant tied to the
// intermediate width the caller actually uses.
std::string ln2Bits(unsigned Width, unsigned Prec) {
  std::vector<uint32_t> Acc(Width / 32 + 2, 0);
  for (unsigned K = 1; K <= Prec; ++K) {
    // Term = 2^(Prec-K) / K, by long division over the limbs.
    std::vector<uint32_t> T(Acc.size(), 0);
    unsigned Bit = Prec - K;
    T[Bit / 32] = 1u << (Bit % 32);
    uint64_t Rem = 0;
    for (size_t I = T.size(); I-- > 0;) {
      uint64_t Cur = (Rem << 32) | T[I];
      T[I] = (uint32_t)(Cur / K);
      Rem = Cur % K;
    }
    uint64_t Carry = 0;
    for (size_t I = 0; I < Acc.size(); ++I) {
      uint64_t S = (uint64_t)Acc[I] + T[I] + Carry;
      Acc[I] = (uint32_t)S;
      Carry = S >> 32;
    }
  }
  std::string Bits(Width, '0');
  for (unsigned I = 0; I < Width; ++I)
    if ((Acc[I / 32] >> (I % 32)) & 1)
      Bits[Width - 1 - I] = '1';
  return Bits;
}

// Terms of exp(r) = sum r^i / i! needed for |r| <= ln2, chosen so the
// truncated tail falls below the intermediate's last bit.
unsigned expTermCount(unsigned Prec) {
  // |r|^(N+1)/(N+1)! < 2^-(Prec+1), with |r| <= ln2 < 0.694.
  double R = 0.6931471805599453, Term = R, Limit = 1.0;
  for (unsigned I = 0; I < Prec + 1; ++I)
    Limit /= 2.0;
  unsigned N = 1;
  while (Term > Limit && N < 64) {
    ++N;
    Term = Term * R / (double)(N + 1);
  }
  return N + 1;
}

} // namespace

SMTExprRef SMTSolverImpl::mkFXPExp(const SMTExprRef &Exp) {
  requireFXP(Exp);
  FXPFormat F = formatOf(Exp->Sort);
  const ExpFormatBound *B = findExpBound(F);
  fatalErrorIf(B == nullptr,
               "Fixed-point exp is supported only on the C _Accum formats "
               "whose hardest-to-round input has been measured; see "
               "scripts/fxp_exp_bounds.txt");

  // Work at P fractional bits, wide enough that the final rounding is
  // decidable for every input of this format.
  const unsigned P = B->RoundingBits + ExpGuardBits;
  // exp(x) = 2^k * exp(r) with x = k*ln2 + r and 0 <= r < ln2, so the
  // series only ever sees a small argument and the scaling is a shift.
  // The intermediate holds exp(r) < 2 plus P fraction bits, the shifted
  // result up to the format's maximum, and the k*ln2 subtraction; the
  // integer part of the source and one sign bit sit on top.
  const unsigned W = P + F.Width + 8;

  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef X = extendRaw(*this, Raw, F.IsSigned, W - F.Width);
  // Bring x to P fractional bits.
  X = mkBVShl(X, mkBVFromDec(P - F.FracBits, W));

  SMTExprRef Ln2 = mkBVFromBin(ln2Bits(W, P), W);

  // k = floor(x / ln2), computed with a signed division that floors.
  SMTExprRef K = mkBVSDiv(X, Ln2);
  SMTExprRef Rem = mkBVSRem(X, Ln2);
  // bvsdiv truncates toward zero; step down when the remainder is
  // negative so r stays in [0, ln2).
  SMTExprRef Zero = mkBVFromDec(0, W);
  SMTExprRef NegRem = mkBVSlt(Rem, Zero);
  K = mkIte(NegRem, mkBVSub(K, mkBVFromDec(1, W)), K);
  SMTExprRef R = mkIte(NegRem, mkBVAdd(Rem, Ln2), Rem);

  // exp(r) by its series, Horner-style from the tail so each step is one
  // multiply and one division by a constant:
  //   acc_i = 1 + r*acc_{i+1}/i
  const unsigned NTerms = expTermCount(P);
  SMTExprRef One =
      mkBVFromBin(std::string(W - P - 1, '0') + "1" + std::string(P, '0'), W);
  SMTExprRef Acc = One;
  // Both factors carry P fractional bits, so their product needs 2*P of
  // them before the shift brings it back: the multiply is done at twice
  // the width and narrowed only once the low bits have been discarded.
  const unsigned W2 = 2 * W;
  SMTExprRef RWide = mkBVZeroExt(W, R);
  for (unsigned I = NTerms; I >= 1; --I) {
    // acc = 1 + (r * acc >> P) / I
    SMTExprRef Prod =
        mkBVLshr(mkBVMul(RWide, mkBVZeroExt(W, Acc)), mkBVFromDec(P, W2));
    if (I > 1)
      Prod = mkBVUDiv(Prod, mkBVFromDec(I, W2));
    Acc = mkBVAdd(One, mkBVExtract(W - 1, 0, Prod));
  }

  // Scale by 2^k. The shift must not be attempted for inputs whose result
  // cannot fit: exp() grows far beyond the intermediate long before the
  // format saturates (x = 47.75 in s8.7 needs ~119 bits), and a shift
  // that overflows wraps to a small value that then looks in range. So
  // the out-of-range cases are decided here, from k alone, and the shift
  // only ever runs where its result is representable.
  //   k >= KMax  =>  saturates;  k <= -KMin  =>  rounds to zero.
  const unsigned KMax = F.Width + 2;
  SMTExprRef Big = mkBVSge(K, mkBVFromDec(KMax, W));
  SMTExprRef Tiny = mkBVSle(K, mkBVSub(Zero, mkBVFromDec(P, W)));
  SMTExprRef SafeK = mkIte(mkOr(Big, Tiny), Zero, K);
  SMTExprRef NegK = mkBVSub(Zero, SafeK);
  SMTExprRef Scaled =
      mkIte(mkBVSlt(SafeK, Zero), mkBVLshr(Acc, NegK), mkBVShl(Acc, SafeK));

  // Round to the format's fraction width, to nearest with ties to even.
  unsigned Shift = P - F.FracBits;
  SMTExprRef Q = mkBVLshr(Scaled, mkBVFromDec(Shift, W));
  SMTExprRef Half = mkBVFromBin(
      std::string(W - Shift, '0') + "1" + std::string(Shift - 1, '0'), W);
  std::string LowMaskBits(W, '0');
  for (unsigned I = 0; I < Shift; ++I)
    LowMaskBits[W - 1 - I] = '1';
  SMTExprRef Low = mkBVAnd(Scaled, mkBVFromBin(LowMaskBits, W));
  SMTExprRef Odd = mkEqual(mkBVExtract(0, 0, Q), mkBVFromDec(1, 1));
  SMTExprRef RoundUp = mkOr(mkBVUgt(Low, Half), mkAnd(mkEqual(Low, Half), Odd));
  Q = mkIte(RoundUp, mkBVAdd(Q, mkBVFromDec(1, W)), Q);

  // Saturate: everything above the format's maximum clamps to it, and the
  // out-of-range inputs set aside before the shift take their answers
  // here rather than from the (meaningless) shifted value.
  SMTExprRef Max = mkBVFromBin(maxRawBits(F, W), W);
  Q = mkIte(mkOr(Big, mkBVUgt(Q, Max)), Max, Q);
  Q = mkIte(Tiny, Zero, Q);
  return rewrapExprImpl(*mkBVExtract(F.Width - 1, 0, Q), Exp->Sort,
                        SMTExprKind::FXPExp);
}

SMTExprRef SMTSolverImpl::mkFXPSqrt(const SMTExprRef &Exp) {
  requireFXP(Exp);
  FXPFormat F = formatOf(Exp->Sort);
  // sqrt(raw/2^n) = sqrt(raw * 2^n) / 2^n, so the result's raw value is
  // the integer square root of raw shifted up by the fraction width.
  // That radicand needs Width + FracBits bits, and its square root needs
  // half as many (rounded up).
  unsigned NBits = F.Width + F.FracBits;
  unsigned Digits = (NBits + 1) / 2;
  // Work at an even radicand width so the digit loop consumes exactly two
  // bits per step.
  unsigned RadWidth = 2 * Digits;
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  // A negative operand has no real square root; zero-extending
  // gives its bits a defined reading rather than a trapping one.
  SMTExprRef Rad = mkBVZeroExt(RadWidth - F.Width, Raw);
  if (F.FracBits != 0)
    Rad = mkBVShl(Rad, mkBVFromDec(F.FracBits, RadWidth));
  // Restoring square root, most significant digit first. Root and
  // remainder are carried at the radicand width; each step brings down
  // two radicand bits, compares against the trial value (4*root + 1 in
  // the shifted frame) and sets the digit when it fits. Exact integer
  // arithmetic throughout, so the result is the true floor of the square
  // root — no approximation, unlike the libc implementations.
  SMTExprRef Root = mkBVFromDec(0, RadWidth);
  SMTExprRef Rem = mkBVFromDec(0, RadWidth);
  SMTExprRef Two = mkBVFromDec(2, RadWidth);
  SMTExprRef One = mkBVFromDec(1, RadWidth);
  for (unsigned I = Digits; I-- > 0;) {
    SMTExprRef Pair =
        mkBVZeroExt(RadWidth - 2, mkBVExtract(2 * I + 1, 2 * I, Rad));
    Rem = mkBVOr(mkBVShl(Rem, Two), Pair);
    SMTExprRef Trial = mkBVOr(mkBVShl(Root, Two), One);
    SMTExprRef Fits = mkBVUge(Rem, Trial);
    Rem = mkIte(Fits, mkBVSub(Rem, Trial), Rem);
    Root =
        mkBVOr(mkBVShl(Root, One), mkIte(Fits, One, mkBVFromDec(0, RadWidth)));
  }
  // The loop leaves Root = floor(sqrt(Rad)) and Rem = Rad - Root^2 exactly.
  // Camada is meant to be an oracle other implementations are checked
  // against, so round to nearest rather than stopping at the floor: the
  // true root lies above the midpoint between Root and Root+1 exactly when
  // Rem > Root, since (Root + 1/2)^2 = Root^2 + Root + 1/4 and Rem is an
  // integer. Ties (Rem == Root) go to even.
  //
  // Nothing in TR 18037 or C pins this direction -- there is no sqrtfx in
  // the standard, and the libc implementations are approximations that
  // disagree with each other -- so the exact operation is ours to choose.
  // The truncating FXP operations elsewhere are NOT free this way: they
  // reproduce C's semantics and must keep doing so.
  SMTExprRef RootOdd = mkEqual(mkBVExtract(0, 0, Root), mkBVFromDec(1, 1));
  SMTExprRef RoundUp =
      mkOr(mkBVUgt(Rem, Root), mkAnd(mkEqual(Rem, Root), RootOdd));
  // Root+1 cannot overflow RadWidth: Root <= sqrt(2^RadWidth - 1) and
  // RadWidth >= 2, so Root is at most 2^(RadWidth/2) - 1.
  Root = mkIte(RoundUp, mkBVAdd(Root, One), Root);

  SMTExprRef Res = mkBVExtract(F.Width - 1, 0, Root);
  // A negative operand has no real square root, and the zero-extension
  // above reads its two's-complement bits as a large positive radicand,
  // producing a plausible in-format number rather than visible garbage
  // (sqrt(-1.0) would read back as -1.0). Pinning those to zero costs
  // one ITE and keeps a wrong answer from looking like a right one.
  if (F.IsSigned)
    Res = mkIte(mkBVSlt(Raw, mkBVFromDec(0, F.Width)), mkBVFromDec(0, F.Width),
                Res);
  return rewrapExprImpl(*Res, Exp->Sort, SMTExprKind::FXPSqrt);
}

// ---------------------------------------------------------------------------
// Fixed-point <-> floating-point conversions
// ---------------------------------------------------------------------------
//
// Both directions run through a floating-point format wide enough to hold
// every intermediate step exactly, so the operation's only rounding is its
// final conversion step. That single rounding is the property composition
// cannot provide: converting to the target format first and scaling by a
// power of two after rounds twice whenever the scale crosses the subnormal
// boundary. Semantics are pinned by the execution oracle (kToFP/kFromFP):
// fixed->float rounds per R (C uses RNE), float->fixed truncates toward
// zero, _Sat clamps with +-infinity at the rails and NaN at zero.

namespace {

// IEEE bit string of +-(2^K + (AddDist == 0 ? 0 : 2^(K-AddDist))) in a
// (EWidth, SigWidth) format. K must be a normal exponent of the format and
// AddDist at most SigWidth.
std::string fpPow2Bits(bool Negative, int64_t K, unsigned AddDist,
                       unsigned EWidth, unsigned SigWidth) {
  std::string Bits(1 + EWidth + SigWidth, '0');
  Bits[0] = Negative ? '1' : '0';
  uint64_t ExpField =
      static_cast<uint64_t>((int64_t(1) << (EWidth - 1)) - 1 + K);
  for (unsigned I = 0; I < EWidth; ++I)
    if ((ExpField >> (EWidth - 1 - I)) & 1)
      Bits[1 + I] = '1';
  if (AddDist != 0)
    Bits[1 + EWidth + AddDist - 1] = '1';
  return Bits;
}

// Smallest FP sort with at least SigWidth significand bits whose normal
// range covers +-MaxExp with headroom (intermediates never go subnormal).
//
// Under the Native encoding the sort must come from {binary32, binary64}:
// backends restrict which native formats exist (bitwuzla rejects
// nonstandard ones, cvc5's default build allows only Float32/Float64), and
// those two are the universal floor wherever native FP exists at all.
// Returns null when neither fits — the caller then computes in the BV
// encoding and bit-bridges the result into the native sort.
SMTSortRef nativeWideFPSortFor(SMTSolverImpl &S, unsigned SigWidth,
                               uint64_t MaxExp) {
  static constexpr std::pair<unsigned, unsigned> Ladder[] = {{8, 23}, {11, 52}};
  for (auto [E, Sig] : Ladder)
    if (Sig >= SigWidth && (uint64_t(1) << (E - 1)) >= MaxExp + 3)
      return S.mkFPSort(E, Sig, FPEncoding::Native);
  return SMTSortRef();
}

// BV-encoded wide sort: any format works, respecting mkFPSort's
// structural bound.
SMTSortRef bvWideFPSortFor(SMTSolverImpl &S, unsigned SigWidth,
                           uint64_t MaxExp) {
  unsigned E = 4;
  while ((uint64_t(1) << (E - 1)) < MaxExp + 3 ||
         2 * (uint64_t(SigWidth) + 1) + 5 > (uint64_t(1) << (E + 1)) - 1)
    ++E;
  return S.mkFPSort(E, SigWidth, FPEncoding::BV);
}

struct FPFXPParts {
  SMTExprRef Scaled; // Exp * 2^FracBits in the exact wide format
  SMTExprRef IsNaN;
  SMTExprRef TooHi; // !(Scaled < maxRaw+1): above range or +infinity
  SMTExprRef TooLo; // !(Scaled > minRaw-1): below range or -infinity
};

FPFXPParts fpToFXPParts(SMTSolverImpl &S, const SMTExprRef &Exp,
                        const FXPFormat &To) {
  SMTSortRef Src = Exp->Sort;
  SMTExprRef Val = Exp;
  unsigned SrcE = Src->getFPExponentWidth();
  unsigned SrcS = Src->getWidth() - 1 - SrcE;
  // Wide holds the widened source exactly (subnormals become normal), the
  // 2^FracBits scale without overflow, and the range bounds exactly.
  uint64_t MaxExp =
      (uint64_t(1) << (SrcE - 1)) + To.FracBits + SrcS + To.Width + 2;
  unsigned WideSig = std::max({SrcS, To.Width, 2u});
  FPEncoding Enc = FPEncoding::BV;
  SMTSortRef Wide;
  if (!Src->isBVFPSort()) {
    Wide = nativeWideFPSortFor(S, WideSig, MaxExp);
    if (Wide) {
      Enc = FPEncoding::Native;
    } else {
      // No universal native format holds the intermediate: reinterpret
      // the source's IEEE bits into the BV encoder and compute there —
      // the result is a raw bit-vector either way. A NaN source may
      // surface as any NaN payload, which the BV encoder still
      // classifies as NaN.
      Val = S.mkBVToIEEEFP(S.mkIEEEFPToBV(Exp),
                           S.mkFPSort(SrcE, SrcS, FPEncoding::BV));
    }
  }
  if (!Wide)
    Wide = bvWideFPSortFor(S, WideSig, MaxExp);
  unsigned WE = Wide->getFPExponentWidth();
  unsigned WS = Wide->getWidth() - 1 - WE;
  SMTExprRef RNE = S.mkRM(RM::ROUND_TO_EVEN, Enc);
  SMTExprRef Scaled = S.mkFPtoFP(Val, Wide, RNE); // exact: Wide covers Src
  if (To.FracBits != 0)
    Scaled = S.mkFPMul(
        Scaled,
        S.mkFPFromBin(fpPow2Bits(false, int64_t(To.FracBits), 0, WE, WS), WE,
                      Enc),
        RNE); // exact power-of-two scale
  FPFXPParts P;
  P.Scaled = Scaled;
  P.IsNaN = S.mkFPIsNaN(Exp);
  // The toward-zero result lands in range iff minRaw-1 < scaled < maxRaw+1
  // (open interval: maxRaw + 0.9 still truncates to maxRaw). Both bounds
  // are a power of two or a two-term sum, exactly representable in Wide.
  // The negated comparisons also classify +-infinity; NaN fails both
  // comparisons and would read as TooHi and TooLo, so callers test IsNaN
  // first.
  SMTExprRef Hi = S.mkFPFromBin(
      fpPow2Bits(false, To.IsSigned ? To.Width - 1 : To.Width, 0, WE, WS), WE,
      Enc);
  // minRaw-1 is -1 unsigned, -(2^(Width-1) + 1) signed (a pure power of
  // two, -2, when Width == 1).
  SMTExprRef Lo =
      !To.IsSigned ? S.mkFPFromBin(fpPow2Bits(true, 0, 0, WE, WS), WE, Enc)
      : To.Width == 1
          ? S.mkFPFromBin(fpPow2Bits(true, 1, 0, WE, WS), WE, Enc)
          : S.mkFPFromBin(fpPow2Bits(true, To.Width - 1, To.Width - 1, WE, WS),
                          WE, Enc);
  P.TooHi = S.mkNot(S.mkFPLt(Scaled, Hi));
  P.TooLo = S.mkNot(S.mkFPGt(Scaled, Lo));
  return P;
}

} // namespace

SMTExprRef SMTSolverImpl::mkFXPToFP(const SMTExprRef &Exp, const SMTSortRef &To,
                                    RM R) {
  requireFXP(Exp);
  fatalErrorIf(!To->isFPSort(), "Expected floating-point target sort");
  FXPFormat From = formatOf(Exp->Sort);
  unsigned WideSig = std::max(From.Width, 2u);
  uint64_t MaxExp = uint64_t(std::max(From.Width, From.FracBits)) + 2;
  // The raw integer converts exactly (wide significand covers the raw
  // width), the 2^-FracBits scale is an exact power-of-two multiply
  // inside the wide range, and the final mkFPtoFP performs the
  // conversion's only rounding, per R. When the target is native but no
  // universal native format holds the intermediate, the whole conversion
  // runs in the BV encoder — including the final rounding, into a
  // BV-encoded twin of the target format — and the resulting bits
  // reinterpret into the native sort (exact, no extra rounding).
  FPEncoding Enc = FPEncoding::BV;
  SMTSortRef Wide, RoundTo = To;
  if (!To->isBVFPSort()) {
    Wide = nativeWideFPSortFor(*this, WideSig, MaxExp);
    if (Wide)
      Enc = FPEncoding::Native;
    else
      RoundTo = mkFPSort(To->getFPExponentWidth(),
                         To->getWidth() - 1 - To->getFPExponentWidth(),
                         FPEncoding::BV);
  }
  if (!Wide)
    Wide = bvWideFPSortFor(*this, WideSig, MaxExp);
  SMTExprRef Rm = mkRM(R, Enc);
  SMTExprRef Raw = mkFXPToRawBV(Exp);
  SMTExprRef Val =
      From.IsSigned ? mkSBVtoFP(Raw, Wide, Rm) : mkUBVtoFP(Raw, Wide, Rm);
  if (From.FracBits != 0) {
    unsigned WE = Wide->getFPExponentWidth();
    unsigned WS = Wide->getWidth() - 1 - WE;
    Val = mkFPMul(
        Val,
        mkFPFromBin(fpPow2Bits(false, -int64_t(From.FracBits), 0, WE, WS), WE,
                    Enc),
        Rm);
  }
  SMTExprRef Res = mkFPtoFP(Val, RoundTo, Rm);
  if (RoundTo != To)
    Res = mkBVToIEEEFP(mkIEEEFPToBV(Res), To);
  return rewrapExprImpl(*Res, To, SMTExprKind::FXPToFP);
}

SMTExprRef SMTSolverImpl::mkFPToFXP(const SMTExprRef &Exp,
                                    const SMTSortRef &To) {
  fatalErrorIf(!Exp->Sort->isFPSort(), "Expected floating-point expression");
  requireFXPSort(To);
  FXPFormat Target = formatOf(To);
  FPFXPParts P = fpToFXPParts(*this, Exp, Target);
  // fp.to_sbv / fp.to_ubv round toward zero across all backends and the
  // BV encoding — C's float->fixed direction (fixed->fixed narrowing
  // floors instead; both oracle-pinned). Out of range, for infinities,
  // and for NaN the result is solver-chosen, matching C's UB; gate with
  // mkFPToFXPOverflow.
  SMTExprRef Raw = Target.IsSigned ? mkFPtoSBV(P.Scaled, Target.Width)
                                   : mkFPtoUBV(P.Scaled, Target.Width);
  return rewrapExprImpl(*Raw, To, SMTExprKind::FPToFXP);
}

SMTExprRef SMTSolverImpl::mkFPToFXPOverflow(const SMTExprRef &Exp,
                                            const SMTSortRef &To) {
  fatalErrorIf(!Exp->Sort->isFPSort(), "Expected floating-point expression");
  requireFXPSort(To);
  FPFXPParts P = fpToFXPParts(*this, Exp, formatOf(To));
  return mkOr(P.IsNaN, mkOr(P.TooHi, P.TooLo));
}

SMTExprRef SMTSolverImpl::mkFPToFXPSat(const SMTExprRef &Exp,
                                       const SMTSortRef &To) {
  fatalErrorIf(!Exp->Sort->isFPSort(), "Expected floating-point expression");
  requireFXPSort(To);
  FXPFormat Target = formatOf(To);
  FPFXPParts P = fpToFXPParts(*this, Exp, Target);
  SMTExprRef Raw = Target.IsSigned ? mkFPtoSBV(P.Scaled, Target.Width)
                                   : mkFPtoUBV(P.Scaled, Target.Width);
  // NaN -> 0 (Clang's _Sat choice; the TR leaves it undefined), rails for
  // out-of-range and +-infinity, toward-zero otherwise. NaN tests first:
  // it fails both comparisons, so TooHi and TooLo both hold for it.
  SMTExprRef Res = mkIte(
      P.IsNaN, mkBVFromDec(0, Target.Width),
      mkIte(P.TooHi,
            mkBVFromBin(maxRawBits(Target, Target.Width), Target.Width),
            mkIte(P.TooLo,
                  mkBVFromBin(minRawBits(Target, Target.Width), Target.Width),
                  Raw)));
  return rewrapExprImpl(*Res, To, SMTExprKind::FPToFXPSat);
}

// ---------------------------------------------------------------------------
// Model query
// ---------------------------------------------------------------------------

SMTResult<SMTSolver::FXPValue> SMTSolverImpl::getFXP(const SMTExprRef &Exp) {
  requireFXP(Exp);
  SMTResult<std::string> Bits = getBVInBin(mkFXPToRawBV(Exp));
  if (!Bits)
    return Bits.error();
  return SMTSolver::FXPValue{std::move(Bits.value()),
                             Exp->Sort->getFXPFracBits(),
                             Exp->Sort->isFXPSignedSort()};
}

} // namespace camada
