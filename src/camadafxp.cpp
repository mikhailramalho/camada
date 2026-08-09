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
// everything else truncates low bits (floor).
//
// Mixed-format operands follow TR 18037's usual arithmetic conversions: the
// operation is computed in the common full-precision format (max integer
// bits, max fractional bits, signed if either operand is signed) and the
// result carries that format.
//
// No solver has a native fixed-point theory, so unlike camadafp.cpp there is
// no native-vs-encoded split here: everything below is built once from the
// public BV surface and works on every backend, including the SMT-LIB pipe.

#include "camadaimpl.h"

#include "camadacommon.h"

#include <algorithm>
#include <string>
#include <utility>

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

SMTExprRef SMTSolverImpl::mkFXPMul(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // The exact product of two W-bit values fits in 2W bits; drop the extra
  // fraction bits of the raw product (floor), then take the low W bits.
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef Prod = mkBVMul(L, R);
  if (P.Fmt.FracBits != 0) {
    SMTExprRef Amount = mkBVFromDec(P.Fmt.FracBits, 2 * P.Fmt.Width);
    Prod = P.Fmt.IsSigned ? mkBVAshr(Prod, Amount) : mkBVLshr(Prod, Amount);
  }
  return rewrapExprImpl(*mkBVExtract(P.Fmt.Width - 1, 0, Prod),
                        mkFXPSort(P.Fmt.Width, P.Fmt.FracBits, P.Fmt.IsSigned),
                        SMTExprKind::FXPMul);
}

SMTExprRef SMTSolverImpl::mkFXPDiv(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  AlignedPair P = alignPair(*this, LHS, RHS);
  // (lhs * 2^N) / rhs at double width: extend first, then scale the
  // dividend — the shift cannot overflow 2W since N <= W. bvsdiv truncates
  // toward zero, matching C division.
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  if (P.Fmt.FracBits != 0)
    L = mkBVShl(L, mkBVFromDec(P.Fmt.FracBits, 2 * P.Fmt.Width));
  SMTExprRef Quot = P.Fmt.IsSigned ? mkBVSDiv(L, R) : mkBVUDiv(L, R);
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
  // Same 2W scaled dividend and toward-zero quotient as mkFXPDiv; clamp
  // instead of truncating. The signed min/-1 case lands above max at 2W
  // and clamps there. The value is meaningful only under !mkFXPDivByZero.
  SMTExprRef L = extendRaw(*this, P.LHS, P.Fmt.IsSigned, P.Fmt.Width);
  SMTExprRef R = extendRaw(*this, P.RHS, P.Fmt.IsSigned, P.Fmt.Width);
  if (P.Fmt.FracBits != 0)
    L = mkBVShl(L, mkBVFromDec(P.Fmt.FracBits, 2 * P.Fmt.Width));
  SMTExprRef Quot = P.Fmt.IsSigned ? mkBVSDiv(L, R) : mkBVUDiv(L, R);
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

SMTExprRef SMTSolverImpl::mkFXPFromBV(const SMTExprRef &Exp,
                                      const SMTSortRef &To) {
  fatalErrorIf(!Exp->Sort->isBVSort(), "Expected bit-vector expression");
  requireFXPSort(To);
  // An integer is a fixed-point value with zero fraction bits; converting
  // is then a format conversion from (width, 0, target signedness).
  // Overflow of this conversion is queryable through mkFXPToFXPOverflow on
  // the same reinterpretation.
  SMTSortRef IntSort = mkFXPSort(Exp->getWidth(), 0, To->isFXPSignedSort());
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
                                            unsigned ToWidth) {
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
  FXPFormat IntTarget{ToWidth, 0, From.IsSigned};
  SMTExprRef Max = mkBVFromBin(maxRawBits(IntTarget, Wide), Wide);
  SMTExprRef Min = mkBVFromBin(minRawBits(IntTarget, Wide), Wide);
  return mkOr(mkBVSgt(Raw, Max), mkBVSlt(Raw, Min));
}

SMTExprRef SMTSolverImpl::mkFXPToBVSat(const SMTExprRef &Exp,
                                       unsigned ToWidth) {
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
  FXPFormat IntTarget{ToWidth, 0, From.IsSigned};
  return rewrapExprImpl(*clampRaw(*this, Raw, Wide, IntTarget,
                                  /*SignedCmp=*/true),
                        mkBVSort(ToWidth), SMTExprKind::FXPToBVSat);
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
