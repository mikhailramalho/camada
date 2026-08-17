// Fixed-point (FXP) fixtures, backend-agnostic. Everything here goes
// through Camada's common-layer BV encoding, so the same fixtures run on
// every native backend and on the SMT-LIB pipeline children.
//
// Verification strategy: an exact integer reference model (numerators are
// raw*1, exact products/quotients computed in int64_t) evaluates every
// operation and predicate; the solver-side encoding is then pinned with a
// single conjunction of constant equalities per operation and format, so a
// SAT answer proves every enumerated case at once. The 4-bit exhaustive
// sweeps enumerate all operand pairs; targeted vectors cover the boundary
// and rounding cases wider sweeps would miss; wide-format properties are
// checked as UNSAT queries over symbolic values (no host arithmetic at
// those widths).

#ifndef CAMADA_REGRESSION_FXP_TEST_H_
#define CAMADA_REGRESSION_FXP_TEST_H_

#include "camada.h"

#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <string>
#include <vector>

namespace camada_fxp_test {

// ---------------------------------------------------------------------------
// Exact reference model
// ---------------------------------------------------------------------------

struct RefFormat {
  unsigned Width;
  unsigned FracBits;
  bool IsSigned;

  int64_t minRaw() const { return IsSigned ? -(int64_t(1) << (Width - 1)) : 0; }
  int64_t maxRaw() const {
    return IsSigned ? (int64_t(1) << (Width - 1)) - 1
                    : (int64_t(1) << Width) - 1;
  }
};

// Interprets the low Width bits of Raw as the format's raw value.
inline int64_t refDecode(const RefFormat &F, uint64_t Raw) {
  Raw &= (F.Width == 64) ? ~uint64_t(0) : ((uint64_t(1) << F.Width) - 1);
  if (F.IsSigned && (Raw >> (F.Width - 1)) != 0)
    return int64_t(Raw) - (int64_t(1) << F.Width);
  return int64_t(Raw);
}

// Two's-complement wrap of a mathematically exact raw value to Width bits.
inline uint64_t refWrap(const RefFormat &F, int64_t Value) {
  // int64_t arithmetic is exact only while formats stay narrow; the widest
  // host-modeled format in these fixtures is 16 bits.
  assert(F.Width <= 16);
  return uint64_t(uint64_t(Value) & ((uint64_t(1) << F.Width) - 1));
}

inline std::string refBits(const RefFormat &F, uint64_t Raw) {
  std::string Bits(F.Width, '0');
  for (unsigned I = 0; I < F.Width; ++I)
    if ((Raw >> I) & 1)
      Bits[F.Width - 1 - I] = '1';
  return Bits;
}

// Floor division of exact integers (the value semantics of the truncating
// right shifts in multiplication and fixed-to-fixed narrowing).
inline int64_t refFloorDiv(int64_t Num, int64_t Den) {
  int64_t Q = Num / Den;
  if ((Num % Den) != 0 && ((Num < 0) != (Den < 0)))
    --Q;
  return Q;
}

struct RefResult {
  uint64_t Raw = 0;      // wrapped result bits (meaningful iff !Overflow)
  bool Overflow = false; // pre-rounding exact result outside the format
  bool DivByZero = false;
};

inline RefResult refAdd(const RefFormat &F, int64_t A, int64_t B) {
  int64_t Exact = int64_t(A) + B;
  return {refWrap(F, Exact), Exact < F.minRaw() || Exact > F.maxRaw(), false};
}

inline RefResult refSub(const RefFormat &F, int64_t A, int64_t B) {
  int64_t Exact = int64_t(A) - B;
  return {refWrap(F, Exact), Exact < F.minRaw() || Exact > F.maxRaw(), false};
}

inline RefResult refNeg(const RefFormat &F, int64_t A) {
  int64_t Exact = -int64_t(A);
  return {refWrap(F, Exact), Exact < F.minRaw() || Exact > F.maxRaw(), false};
}

inline RefResult refMul(const RefFormat &F, int64_t A, int64_t B) {
  // Exact product in raw scale is A*B/2^N; the encoding floors it. The
  // overflow predicate tests the pre-rounding exact value.
  int64_t Prod = int64_t(A) * B;
  int64_t Scale = int64_t(1) << F.FracBits;
  RefResult R;
  R.Overflow =
      Prod < int64_t(F.minRaw()) * Scale || Prod > int64_t(F.maxRaw()) * Scale;
  R.Raw = refWrap(F, refFloorDiv(Prod, Scale));
  return R;
}

inline RefResult refDiv(const RefFormat &F, int64_t A, int64_t B) {
  RefResult R;
  if (B == 0) {
    R.DivByZero = true;
    return R;
  }
  // Exact quotient in raw scale is (A*2^N)/B; the encoding floors it (the
  // oracle-pinned direction). Overflow compares the exact rational bounds:
  // for B > 0, exact > max iff A*2^N > max*B (and flipped for B < 0).
  int64_t Num = int64_t(A) << F.FracBits;
  int64_t MaxB = int64_t(F.maxRaw()) * B;
  int64_t MinB = int64_t(F.minRaw()) * B;
  R.Overflow =
      (B > 0) ? (Num > MaxB || Num < MinB) : (Num < MaxB || Num > MinB);
  R.Raw = refWrap(F, refFloorDiv(Num, B)); // floor (Clang sdiv.fix)
  return R;
}

// ---------------------------------------------------------------------------
// Saturating reference model (TR 18037 `_Sat`): the exact rational result
// clamps to the format bounds; only in-range results round (floor for
// multiplication and narrowing, toward zero for division and to-integer).
// Deliberately written from the TR semantics — clamp-the-exact-value —
// rather than mirroring the encoding's clamp-the-rounded-value shape, so
// the fixtures also pin the output equivalence of the two.
// ---------------------------------------------------------------------------

inline int64_t refClamp(const RefFormat &F, int64_t Exact) {
  if (Exact < F.minRaw())
    return F.minRaw();
  if (Exact > F.maxRaw())
    return F.maxRaw();
  return Exact;
}

inline uint64_t refAddSat(const RefFormat &F, int64_t A, int64_t B) {
  return refWrap(F, refClamp(F, A + B));
}

inline uint64_t refSubSat(const RefFormat &F, int64_t A, int64_t B) {
  return refWrap(F, refClamp(F, A - B));
}

inline uint64_t refNegSat(const RefFormat &F, int64_t A) {
  return refWrap(F, refClamp(F, -A));
}

inline uint64_t refMulSat(const RefFormat &F, int64_t A, int64_t B) {
  int64_t Prod = A * B;
  int64_t Scale = int64_t(1) << F.FracBits;
  if (Prod < F.minRaw() * Scale)
    return refWrap(F, F.minRaw());
  if (Prod > F.maxRaw() * Scale)
    return refWrap(F, F.maxRaw());
  return refWrap(F, refFloorDiv(Prod, Scale));
}

// Precondition: B != 0 (division by zero stays UB for _Sat types).
inline uint64_t refDivSat(const RefFormat &F, int64_t A, int64_t B) {
  int64_t Num = A << F.FracBits;
  int64_t MaxB = F.maxRaw() * B;
  int64_t MinB = F.minRaw() * B;
  bool AboveMax = (B > 0) ? Num > MaxB : Num < MaxB;
  bool BelowMin = (B > 0) ? Num < MinB : Num > MinB;
  if (AboveMax)
    return refWrap(F, F.maxRaw());
  if (BelowMin)
    return refWrap(F, F.minRaw());
  return refWrap(F, refFloorDiv(Num, B)); // floor (Clang sdiv.fix)
}

inline uint64_t refShlSat(const RefFormat &F, int64_t A, unsigned Amount) {
  return refWrap(F, refClamp(F, A * (int64_t(1) << Amount)));
}

// ---------------------------------------------------------------------------
// Solver-side helpers
// ---------------------------------------------------------------------------

inline camada::SMTSortRef mkSort(const camada::SMTSolverRef &S,
                                 const RefFormat &F) {
  return S->mkFXPSort(F.Width, F.FracBits, F.IsSigned);
}

inline camada::SMTExprRef mkConst(const camada::SMTSolverRef &S,
                                  const RefFormat &F, uint64_t Raw) {
  return S->mkFXPFromBin(refBits(F, Raw), mkSort(S, F));
}

// Asserts the conjunction and requires it satisfiable: every conjunct is a
// ground equality over constants, so SAT proves all of them at once.
inline void requireAllHold(const camada::SMTSolverRef &S,
                           const std::vector<camada::SMTExprRef> &Conjuncts) {
  REQUIRE(!Conjuncts.empty());
  camada::SMTExprRef All = Conjuncts.front();
  for (std::size_t I = 1; I < Conjuncts.size(); ++I)
    All = S->mkAnd(All, Conjuncts[I]);
  S->addConstraint(All);
  REQUIRE(S->check() == camada::checkResult::SAT);
}

inline camada::SMTExprRef boolIs(const camada::SMTSolverRef &S,
                                 const camada::SMTExprRef &Pred,
                                 bool Expected) {
  return Expected ? Pred : S->mkNot(Pred);
}

// The three 4-bit formats the exhaustive sweeps run: signed and unsigned
// mid-fraction, plus the all-fraction unsigned shape TR 18037 gives
// unsigned _Fract.
inline std::vector<RefFormat> sweepFormats() {
  return {{4, 2, true}, {4, 2, false}, {4, 4, false}};
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

// Exhaustive 4-bit sweep: every operand pair, every operation, value and
// predicate, against the exact reference model. One solver check per
// (format, operation).
inline void fxp_exhaustive_semantics(const camada::SMTSolverRef &solver) {
  enum class Op { Add, Sub, Mul, Div, Neg };
  for (const RefFormat &F : sweepFormats()) {
    for (Op O : {Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Neg}) {
      solver->reset();
      std::vector<camada::SMTExprRef> Conjuncts;
      const uint64_t Count = uint64_t(1) << F.Width;
      for (uint64_t RA = 0; RA < Count; ++RA) {
        for (uint64_t RB = 0; RB < (O == Op::Neg ? 1 : Count); ++RB) {
          int64_t A = refDecode(F, RA);
          int64_t B = refDecode(F, RB);
          camada::SMTExprRef EA = mkConst(solver, F, RA);
          camada::SMTExprRef EB = mkConst(solver, F, RB);

          RefResult Ref;
          camada::SMTExprRef Value;
          camada::SMTExprRef Pred;
          switch (O) {
          case Op::Add:
            Ref = refAdd(F, A, B);
            Value = solver->mkFXPAdd(EA, EB);
            Pred = solver->mkFXPAddOverflow(EA, EB);
            break;
          case Op::Sub:
            Ref = refSub(F, A, B);
            Value = solver->mkFXPSub(EA, EB);
            Pred = solver->mkFXPSubOverflow(EA, EB);
            break;
          case Op::Mul:
            Ref = refMul(F, A, B);
            Value = solver->mkFXPMul(EA, EB, camada::FXPRM::TowardNegative);
            Pred = solver->mkFXPMulOverflow(EA, EB);
            break;
          case Op::Div:
            Ref = refDiv(F, A, B);
            Value = solver->mkFXPDiv(EA, EB, camada::FXPRM::TowardNegative);
            Pred = solver->mkFXPDivOverflow(EA, EB);
            Conjuncts.push_back(
                boolIs(solver, solver->mkFXPDivByZero(EB), Ref.DivByZero));
            break;
          case Op::Neg:
            Ref = refNeg(F, A);
            Value = solver->mkFXPNeg(EA);
            Pred = solver->mkFXPNegOverflow(EA);
            break;
          }
          Conjuncts.push_back(boolIs(solver, Pred, Ref.Overflow));
          // The value contract only holds when the operation is defined.
          if (!Ref.DivByZero)
            Conjuncts.push_back(
                solver->mkFXPEqual(Value, mkConst(solver, F, Ref.Raw)));
        }
      }
      requireAllHold(solver, Conjuncts);
    }
  }
}

// Boundary vectors: exact results just outside the representable range
// whose truncation lands back on a boundary — the predicate must still
// report them (pre-rounding semantics).
inline void
fxp_boundary_overflow_semantics(const camada::SMTSolverRef &solver) {
  RefFormat F{8, 4, true}; // Q3.4: raws in [-128, 127], max value 127/16
  // 89 * 23 = 2047: exact product raw 2047/16 in (max*16 = 2032, 2048),
  // truncates to 127 = max. Exact result > max, so this IS an overflow.
  {
    camada::SMTExprRef A = mkConst(solver, F, 89);
    camada::SMTExprRef B = mkConst(solver, F, 23);
    solver->addConstraint(solver->mkFXPMulOverflow(A, B));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    solver->reset();
    A = mkConst(solver, F, 89);
    B = mkConst(solver, F, 23);
    // ... and the truncated value is exactly the boundary.
    solver->addConstraint(solver->mkFXPEqual(
        solver->mkFXPMul(A, B, camada::FXPRM::TowardNegative),
        mkConst(solver, F, 127)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }
  // 127 * 16 = 2032 = max*16 exactly: representable, NOT an overflow.
  {
    solver->reset();
    camada::SMTExprRef A = mkConst(solver, F, 127);
    camada::SMTExprRef B = mkConst(solver, F, 16);
    solver->addConstraint(solver->mkFXPMulOverflow(A, B));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }
  // Division analog: 127/16 divided by 63/64... pick raws A=127, B=15:
  // exact = 127*16/15 = 135.4667 > 127 => overflow, truncation would give
  // 135 which wraps; and A=127, B=16 (1.0) => exact 127, no overflow.
  {
    solver->reset();
    camada::SMTExprRef A = mkConst(solver, F, 127);
    solver->addConstraint(solver->mkFXPDivOverflow(A, mkConst(solver, F, 15)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    solver->reset();
    A = mkConst(solver, F, 127);
    solver->addConstraint(solver->mkFXPDivOverflow(A, mkConst(solver, F, 16)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }
}

// Sign-sensitive rounding vectors: division and multiplication floor
// (the oracle-pinned Clang direction — see scripts/fxp_oracle_gen.py),
// fixed-to-integer truncates toward zero (the one direction TR 18037
// specifies), fixed-to-fixed narrowing floors.
inline void fxp_rounding_semantics(const camada::SMTSolverRef &solver) {
  RefFormat F{8, 4, true};
  auto C = [&](int64_t Raw) {
    return mkConst(solver, F, uint64_t(Raw) & 0xFF);
  };
  std::vector<camada::SMTExprRef> Conjuncts;
  // (-3/16) / 2.0: exact raw quotient -1.5, not representable; floor
  // gives raw -2 (toward zero would give -1 — Clang floors, per the
  // execution oracle).
  Conjuncts.push_back(solver->mkFXPEqual(
      solver->mkFXPDiv(C(-3), C(32), camada::FXPRM::TowardNegative), C(-2)));
  // (3/16) / 2.0: exact raw quotient 1.5 -> raw 1.
  Conjuncts.push_back(solver->mkFXPEqual(
      solver->mkFXPDiv(C(3), C(32), camada::FXPRM::TowardNegative), C(1)));
  // (-1/16) * (8/16): exact -0.5 raw; floor -> -1 raw (not 0).
  Conjuncts.push_back(solver->mkFXPEqual(
      solver->mkFXPMul(C(-1), C(8), camada::FXPRM::TowardNegative), C(-1)));
  // ( 1/16) * (8/16): exact 0.5 raw; floor -> 0 raw.
  Conjuncts.push_back(solver->mkFXPEqual(
      solver->mkFXPMul(C(1), C(8), camada::FXPRM::TowardNegative), C(0)));
  requireAllHold(solver, Conjuncts);

  // Fixed -> integer rounds toward zero: -1.5 -> -1 (a plain arithmetic
  // shift would floor to -2).
  solver->reset();
  camada::SMTExprRef MinusOneHalf = mkConst(solver, F, uint64_t(-24) & 0xFF);
  camada::SMTExprRef AsInt =
      solver->mkFXPToBV(MinusOneHalf, 8, camada::FXPRM::TowardZero);
  solver->addConstraint(solver->mkEqual(AsInt, solver->mkBVFromDec(-1, 8)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Fixed -> fixed narrowing floors: -1.75 in Q3.4 (raw -28) into Q6.1 is
  // exactly -3.5 at one fraction bit, which floors to raw -4 = -2.0 — the
  // documented floor behavior, distinct from the toward-zero -3 = -1.5.
  solver->reset();
  camada::SMTExprRef MinusOneQ3 = mkConst(solver, F, uint64_t(-28) & 0xFF);
  RefFormat Narrow{8, 1, true};
  camada::SMTExprRef Converted = solver->mkFXPToFXP(
      MinusOneQ3, mkSort(solver, Narrow), camada::FXPRM::TowardNegative);
  solver->addConstraint(solver->mkFXPEqual(
      Converted, mkConst(solver, Narrow, uint64_t(-4) & 0xFF)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

// Conversion matrix across widths, fraction splits, and signedness —
// including formats past 64 bits, where properties are checked over
// symbolic values instead of host arithmetic.
inline void fxp_conversion_matrix(const camada::SMTSolverRef &solver) {
  // Exhaustive: every 4-bit value through every conversion pair, checked
  // for the exact-value invariant "widening is exact and overflow-free".
  std::vector<RefFormat> Formats = {
      {4, 2, true}, {4, 2, false}, {4, 4, false}, {4, 0, true}};
  for (const RefFormat &From : Formats) {
    // A format that embeds From: doubled integer and fraction room.
    RefFormat To{From.Width * 4, From.FracBits * 2, true};
    solver->reset();
    std::vector<camada::SMTExprRef> Conjuncts;
    for (uint64_t Raw = 0; Raw < (uint64_t(1) << From.Width); ++Raw) {
      camada::SMTExprRef V = mkConst(solver, From, Raw);
      camada::SMTSortRef ToSort = mkSort(solver, To);
      // Widening never overflows...
      Conjuncts.push_back(solver->mkNot(solver->mkFXPToFXPOverflow(
          V, ToSort, camada::FXPRM::TowardNegative)));
      // ...and is exact: converting up compares equal to the original
      // (mkFXPEqual scale-aligns across the two formats).
      Conjuncts.push_back(solver->mkFXPEqual(
          solver->mkFXPToFXP(V, ToSort, camada::FXPRM::TowardNegative), V));
    }
    requireAllHold(solver, Conjuncts);
  }

  // Signedness-changing narrow: unsigned 4.0 (raw 8 in U2.2) into signed
  // Q1.2 (max 3/4): overflow.
  {
    solver->reset();
    RefFormat U{4, 2, false}, S4{4, 2, true};
    camada::SMTExprRef V = mkConst(solver, U, 8);
    solver->addConstraint(solver->mkFXPToFXPOverflow(
        V, mkSort(solver, S4), camada::FXPRM::TowardNegative));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Negative into unsigned: overflow.
  {
    solver->reset();
    RefFormat S4{4, 2, true}, U{4, 2, false};
    camada::SMTExprRef V = mkConst(solver, S4, uint64_t(-1) & 0xF);
    solver->addConstraint(solver->mkFXPToFXPOverflow(
        V, mkSort(solver, U), camada::FXPRM::TowardNegative));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Wide formats (past 64 bits, 128-bit-plus intermediates): widening a
  // symbolic Q34.35 into Q69.70 is exact and overflow-free for all values.
  {
    solver->reset();
    camada::SMTSortRef WideSrc = solver->mkFXPSort(70, 35, true);
    camada::SMTSortRef WideDst = solver->mkFXPSort(140, 70, true);
    camada::SMTExprRef X = solver->mkSymbol("fxp_wide_x", WideSrc);
    solver->addConstraint(
        solver->mkFXPToFXPOverflow(X, WideDst, camada::FXPRM::TowardNegative));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
    solver->reset();
    WideSrc = solver->mkFXPSort(70, 35, true);
    WideDst = solver->mkFXPSort(140, 70, true);
    X = solver->mkSymbol("fxp_wide_x", WideSrc);
    solver->addConstraint(solver->mkNot(solver->mkFXPEqual(
        solver->mkFXPToFXP(X, WideDst, camada::FXPRM::TowardNegative), X)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }

  // Integer bridges: mkFXPFromBV embeds exactly (round-trip through
  // mkFXPToBV is the identity on in-range integers), toward-zero on the way
  // back is covered by fxp_rounding_semantics.
  for (bool SrcSigned : {true, false}) {
    solver->reset();
    camada::SMTSortRef Fmt = solver->mkFXPSort(16, 4, true);
    camada::SMTExprRef I = solver->mkSymbol("fxp_int_x", solver->mkBVSort(8));
    camada::SMTExprRef AsFXP = solver->mkFXPFromBV(I, SrcSigned, Fmt);
    camada::SMTExprRef Back =
        solver->mkFXPToBV(AsFXP, 8, camada::FXPRM::TowardZero);
    solver->addConstraint(solver->mkNot(solver->mkEqual(Back, I)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }

  // Source signedness governs the value: the same bits 0xFF are -1 as a
  // signed int8 and 255 as a uint8, independent of the (signed) target
  // format. Q11.4: -1 -> raw 0xFFF0, 255 -> raw 0x0FF0.
  {
    solver->reset();
    camada::SMTSortRef Fmt = solver->mkFXPSort(16, 4, true);
    camada::SMTExprRef Bits = solver->mkBVFromDec(0xFF, 8);
    solver->addConstraint(
        solver->mkFXPEqual(solver->mkFXPFromBV(Bits, true, Fmt),
                           solver->mkFXPFromBin("1111111111110000", Fmt)));
    solver->addConstraint(
        solver->mkFXPEqual(solver->mkFXPFromBV(Bits, false, Fmt),
                           solver->mkFXPFromBin("0000111111110000", Fmt)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }
}

// Mixed formats: the operation computes in the common full-precision
// format and comparisons scale-align.
inline void fxp_mixed_format_semantics(const camada::SMTSolverRef &solver) {
  RefFormat A{8, 4, true};  // Q3.4
  RefFormat B{6, 2, false}; // U4.2
  // 1.25 (raw 20 in Q3.4) + 2.75 (raw 11 in U4.2) = 4.0. Common format:
  // int bits max(3,4)=4, frac max(4,2)=4, signed => Q4.4, width 9.
  camada::SMTExprRef EA = mkConst(solver, A, 20);
  camada::SMTExprRef EB = mkConst(solver, B, 11);
  camada::SMTExprRef Sum = solver->mkFXPAdd(EA, EB);
  REQUIRE(Sum->Sort->getWidth() == 9);
  REQUIRE(Sum->Sort->getFXPFracBits() == 4);
  REQUIRE(Sum->Sort->isFXPSignedSort());
  RefFormat Common{9, 4, true};
  solver->addConstraint(solver->mkFXPEqual(Sum, mkConst(solver, Common, 64)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Cross-format comparison: 1.25 (Q3.4) < 2.75 (U4.2).
  solver->reset();
  EA = mkConst(solver, A, 20);
  EB = mkConst(solver, B, 11);
  solver->addConstraint(solver->mkFXPLt(EA, EB));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  solver->reset();
  EA = mkConst(solver, A, 20);
  EB = mkConst(solver, B, 11);
  solver->addConstraint(solver->mkFXPGe(EA, EB));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// Shifts: value semantics and the shifted-out-bits overflow predicate.
inline void fxp_shift_semantics(const camada::SMTSolverRef &solver) {
  RefFormat F{8, 4, true};
  std::vector<camada::SMTExprRef> Conjuncts;
  auto C = [&](int64_t Raw) {
    return mkConst(solver, F, uint64_t(Raw) & 0xFF);
  };
  // 1.5 << 1 = 3.0; -1.5 << 1 = -3.0.
  Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPShl(C(24), 1), C(48)));
  Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPShl(C(-24), 1), C(-48)));
  // 3.0 >> 1 = 1.5; -3.0 >> 1 = -1.5 (arithmetic, exact here).
  Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPShr(C(48), 1), C(24)));
  Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPShr(C(-48), 1), C(-24)));
  // Shl overflow: 4.0 << 1 = 8.0 overflows Q3.4 (max ~7.94); 2.0 << 1 fits.
  Conjuncts.push_back(boolIs(solver, solver->mkFXPShlOverflow(C(64), 1), true));
  Conjuncts.push_back(
      boolIs(solver, solver->mkFXPShlOverflow(C(32), 1), false));
  // Signed: -8.0 << 1 leaves the format even though the sign survives.
  Conjuncts.push_back(
      boolIs(solver, solver->mkFXPShlOverflow(C(-128), 1), true));
  requireAllHold(solver, Conjuncts);
}

// FXP values inside generic constructs: symbols, ITE, arrays, push/pop,
// raw-BV round trips, and exact model extraction.
inline void fxp_model_and_constructs(const camada::SMTSolverRef &solver) {
  RefFormat F{8, 4, true};
  camada::SMTSortRef Fmt = mkSort(solver, F);

  // Symbol + model query: x == 2.5 => getFXP(x) returns the exact raw bits.
  camada::SMTExprRef X = solver->mkSymbol("fxp_x", Fmt);
  solver->addConstraint(solver->mkFXPEqual(X, mkConst(solver, F, 40)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto Val = solver->getFXP(X);
  REQUIRE(Val);
  REQUIRE(Val.value().RawBits == refBits(F, 40));
  REQUIRE(Val.value().FracBits == 4);
  REQUIRE(Val.value().IsSigned);

  // Raw-BV reinterpretation round trip is the identity.
  solver->reset();
  Fmt = mkSort(solver, F);
  X = solver->mkSymbol("fxp_x", Fmt);
  camada::SMTExprRef RoundTrip =
      solver->mkFXPFromRawBV(solver->mkFXPToRawBV(X), Fmt);
  solver->addConstraint(solver->mkNot(solver->mkFXPEqual(RoundTrip, X)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // ITE over FXP values.
  solver->reset();
  Fmt = mkSort(solver, F);
  camada::SMTExprRef Cond = solver->mkSymbol("fxp_c", solver->mkBoolSort());
  camada::SMTExprRef Ite =
      solver->mkIte(Cond, mkConst(solver, F, 16), mkConst(solver, F, 32));
  solver->addConstraint(solver->mkFXPEqual(Ite, mkConst(solver, F, 32)));
  solver->addConstraint(Cond);
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Arrays with FXP elements.
  solver->reset();
  Fmt = mkSort(solver, F);
  camada::SMTSortRef Arr = solver->mkArraySort(solver->mkBVSort(4), Fmt);
  camada::SMTExprRef A = solver->mkSymbol("fxp_arr", Arr);
  camada::SMTExprRef Idx = solver->mkBVFromDec(3, 4);
  camada::SMTExprRef Stored =
      solver->mkArrayStore(A, Idx, mkConst(solver, F, 24));
  solver->addConstraint(solver->mkNot(solver->mkFXPEqual(
      solver->mkArraySelect(Stored, Idx), mkConst(solver, F, 24))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Push/pop: a constraint inside a scope disappears after pop.
  solver->reset();
  Fmt = mkSort(solver, F);
  X = solver->mkSymbol("fxp_x", Fmt);
  solver->addConstraint(solver->mkFXPGt(X, mkConst(solver, F, 0)));
  solver->push();
  solver->addConstraint(solver->mkFXPLt(X, mkConst(solver, F, 0)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
  solver->pop();
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

// Exhaustive 4-bit sweep of the saturating variants against the exact
// reference. Division-by-zero pairs are skipped for DivSat (the value is
// meaningful only under !mkFXPDivByZero, same as the plain division).
inline void fxp_sat_exhaustive_semantics(const camada::SMTSolverRef &solver) {
  enum class Op { Add, Sub, Mul, Div, Neg };
  for (const RefFormat &F : sweepFormats()) {
    for (Op O : {Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Neg}) {
      solver->reset();
      std::vector<camada::SMTExprRef> Conjuncts;
      const uint64_t Count = uint64_t(1) << F.Width;
      for (uint64_t RA = 0; RA < Count; ++RA) {
        for (uint64_t RB = 0; RB < (O == Op::Neg ? 1 : Count); ++RB) {
          int64_t A = refDecode(F, RA);
          int64_t B = refDecode(F, RB);
          camada::SMTExprRef EA = mkConst(solver, F, RA);
          camada::SMTExprRef EB = mkConst(solver, F, RB);

          uint64_t Ref = 0;
          camada::SMTExprRef Value;
          switch (O) {
          case Op::Add:
            Ref = refAddSat(F, A, B);
            Value = solver->mkFXPAddSat(EA, EB);
            break;
          case Op::Sub:
            Ref = refSubSat(F, A, B);
            Value = solver->mkFXPSubSat(EA, EB);
            break;
          case Op::Mul:
            Ref = refMulSat(F, A, B);
            Value = solver->mkFXPMulSat(EA, EB, camada::FXPRM::TowardNegative);
            break;
          case Op::Div:
            if (B == 0)
              continue;
            Ref = refDivSat(F, A, B);
            Value = solver->mkFXPDivSat(EA, EB, camada::FXPRM::TowardNegative);
            break;
          case Op::Neg:
            Ref = refNegSat(F, A);
            Value = solver->mkFXPNegSat(EA);
            break;
          }
          Conjuncts.push_back(
              solver->mkFXPEqual(Value, mkConst(solver, F, Ref)));
        }
      }
      requireAllHold(solver, Conjuncts);
    }
  }
}

// Exhaustive saturating shifts over every amount below the width.
inline void fxp_sat_shift_semantics(const camada::SMTSolverRef &solver) {
  for (const RefFormat &F : sweepFormats()) {
    solver->reset();
    std::vector<camada::SMTExprRef> Conjuncts;
    const uint64_t Count = uint64_t(1) << F.Width;
    for (unsigned Amount = 0; Amount < F.Width; ++Amount) {
      for (uint64_t RA = 0; RA < Count; ++RA) {
        int64_t A = refDecode(F, RA);
        camada::SMTExprRef EA = mkConst(solver, F, RA);
        Conjuncts.push_back(
            solver->mkFXPEqual(solver->mkFXPShlSat(EA, Amount),
                               mkConst(solver, F, refShlSat(F, A, Amount))));
      }
    }
    requireAllHold(solver, Conjuncts);
  }
}

// Saturating conversions: every sweep-format pair (fixed-to-fixed) and
// every source against 2/4/8-bit integer targets, exhaustively.
inline void fxp_sat_conversion_semantics(const camada::SMTSolverRef &solver) {
  // Exact rational compare across formats: bring value and target bounds
  // to the larger fraction scale, clamp, floor only when in range.
  auto toFXPSatRef = [](const RefFormat &From, const RefFormat &To,
                        int64_t A) -> uint64_t {
    unsigned Scale = std::max(From.FracBits, To.FracBits);
    int64_t V = A << (Scale - From.FracBits);
    int64_t Max = To.maxRaw() << (Scale - To.FracBits);
    int64_t Min = To.minRaw() << (Scale - To.FracBits);
    if (V > Max)
      return uint64_t(To.maxRaw()) & ((uint64_t(1) << To.Width) - 1);
    if (V < Min)
      return uint64_t(To.minRaw()) & ((uint64_t(1) << To.Width) - 1);
    int64_t R = refFloorDiv(V, int64_t(1) << (Scale - To.FracBits));
    return uint64_t(R) & ((uint64_t(1) << To.Width) - 1);
  };
  auto toBVSatRef = [](const RefFormat &From, unsigned ToWidth, bool ToSigned,
                       int64_t A) -> uint64_t {
    RefFormat IntTarget{ToWidth, 0, ToSigned};
    int64_t Trunc = A / (int64_t(1) << From.FracBits); // toward zero
    if (Trunc < IntTarget.minRaw())
      Trunc = IntTarget.minRaw();
    if (Trunc > IntTarget.maxRaw())
      Trunc = IntTarget.maxRaw();
    return uint64_t(Trunc) & ((uint64_t(1) << ToWidth) - 1);
  };

  for (const RefFormat &From : sweepFormats()) {
    const uint64_t Count = uint64_t(1) << From.Width;
    for (const RefFormat &To : sweepFormats()) {
      solver->reset();
      std::vector<camada::SMTExprRef> Conjuncts;
      for (uint64_t RA = 0; RA < Count; ++RA) {
        int64_t A = refDecode(From, RA);
        camada::SMTExprRef EA = mkConst(solver, From, RA);
        Conjuncts.push_back(solver->mkFXPEqual(
            solver->mkFXPToFXPSat(EA, mkSort(solver, To),
                                  camada::FXPRM::TowardNegative),
            mkConst(solver, To, toFXPSatRef(From, To, A))));
      }
      requireAllHold(solver, Conjuncts);
    }
    for (unsigned ToWidth : {2u, 4u, 8u}) {
      // Both target signednesses: the clamp range is the TARGET type's —
      // a negative source clamps to zero for an unsigned target.
      for (bool ToSigned : {true, false}) {
        solver->reset();
        std::vector<camada::SMTExprRef> Conjuncts;
        for (uint64_t RA = 0; RA < Count; ++RA) {
          int64_t A = refDecode(From, RA);
          camada::SMTExprRef EA = mkConst(solver, From, RA);
          RefFormat IntF{ToWidth, 0, ToSigned};
          std::string Bits =
              refBits(IntF, toBVSatRef(From, ToWidth, ToSigned, A));
          Conjuncts.push_back(
              solver->mkEqual(solver->mkFXPToBVSat(EA, ToWidth, ToSigned,
                                                   camada::FXPRM::TowardZero),
                              solver->mkBVFromBin(Bits, ToWidth)));
        }
        requireAllHold(solver, Conjuncts);
      }
    }
  }
}

// Runtime-amount shifts agree with the constant-amount variants for
// every amount below the width — value, overflow predicate, and sat
// clamp — proven over a fully symbolic operand per (format, amount).
inline void fxp_symbolic_shift_semantics(const camada::SMTSolverRef &solver) {
  for (const RefFormat &F : sweepFormats()) {
    for (unsigned K = 0; K < F.Width; ++K) {
      solver->reset();
      camada::SMTExprRef X = solver->mkFXPFromRawBV(
          solver->mkSymbol("shx", solver->mkBVSort(F.Width)),
          mkSort(solver, F));
      camada::SMTExprRef KE = solver->mkBVFromDec(K, F.Width);
      camada::SMTExprRef Same = solver->mkAnd(
          solver->mkAnd(solver->mkFXPEqual(solver->mkFXPShlExpr(X, KE),
                                           solver->mkFXPShl(X, K)),
                        solver->mkFXPEqual(solver->mkFXPShrExpr(X, KE),
                                           solver->mkFXPShr(X, K))),
          solver->mkAnd(solver->mkFXPEqual(solver->mkFXPShlSatExpr(X, KE),
                                           solver->mkFXPShlSat(X, K)),
                        solver->mkEqual(solver->mkFXPShlOverflowExpr(X, KE),
                                        solver->mkFXPShlOverflow(X, K))));
      solver->addConstraint(solver->mkNot(Same));
      REQUIRE(solver->check() == camada::checkResult::UNSAT);
    }
  }
}

// roundfx: round to nearest at a chosen fraction width, ties toward +inf,
// saturating to the format maximum when the half-ulp bias overflows. The
// reference is written from the TR/libc semantics (bias then mask, with an
// exact-arithmetic overflow test), independently of the encoding's shape.
// Written from the value semantics — round the exact quotient to an
// integer per the tie rule, then rescale — rather than mirroring the
// encoding's bias-and-mask shape, so the fixtures pin that the two agree.
inline uint64_t refRound(const RefFormat &F, int64_t A, unsigned Digits,
                         camada::FXPRM Tie) {
  if (Digits >= F.FracBits)
    return refWrap(F, A);
  unsigned Shift = F.FracBits - Digits;
  int64_t Unit = int64_t(1) << Shift;
  int64_t Q = refFloorDiv(A, Unit); // floor, so Rem is never negative
  int64_t Rem = A - Q * Unit;
  int64_t Half = Unit / 2;
  // The directed modes never look at the halfway point.
  switch (Tie) {
  case camada::FXPRM::TowardNegative:
    break; // Q is already the floor
  case camada::FXPRM::TowardPositive:
    if (Rem)
      ++Q;
    break;
  case camada::FXPRM::TowardZero:
    if (Rem && A < 0)
      ++Q; // floor is one unit too low for negatives
    break;
  case camada::FXPRM::NearestTiesTowardPositive:
  case camada::FXPRM::NearestTiesAwayFromZero:
  case camada::FXPRM::NearestTiesToEven:
    if (Rem > Half)
      ++Q;
    else if (Rem == Half) {
      if (Tie == camada::FXPRM::NearestTiesTowardPositive)
        ++Q;
      else if (Tie == camada::FXPRM::NearestTiesAwayFromZero) {
        if (A >= 0)
          ++Q;
      } else
        Q += Q & 1;
    }
    break;
  }
  int64_t V = Q * Unit;
  return refWrap(F, V > F.maxRaw() ? F.maxRaw() : V);
}

// absfx and countlsfx. Both references are written from the TR/libc
// definitions rather than the encoding's shape: abs saturates at the most
// negative value (which has no positive counterpart), and countls is the
// number of redundant sign copies, i.e. how far the value can shift left
// before its sign changes.
inline uint64_t refAbs(const RefFormat &F, int64_t A) {
  if (!F.IsSigned)
    return refWrap(F, A);
  if (A == F.minRaw())
    return refWrap(F, F.maxRaw());
  return refWrap(F, A < 0 ? -A : A);
}

inline unsigned refCountls(const RefFormat &F, uint64_t Raw) {
  uint64_t Mask = (uint64_t(1) << F.Width) - 1;
  uint64_t V = Raw & Mask;
  if (F.IsSigned && (V >> (F.Width - 1)))
    V = (~V) & Mask;
  unsigned Lead = 0;
  for (int I = int(F.Width) - 1; I >= 0; --I) {
    if ((V >> I) & 1)
      break;
    ++Lead;
  }
  return Lead - (F.IsSigned ? 1 : 0);
}

inline void fxp_abs_countls_semantics(const camada::SMTSolverRef &solver) {
  // Exhaustive over every format up to 6 bits, both signednesses.
  for (unsigned Width = 2; Width <= 6; ++Width) {
    for (unsigned Frac = 0; Frac < Width; ++Frac) {
      for (bool Signed : {true, false}) {
        if (Signed && Frac + 1 > Width - 1)
          continue;
        RefFormat F{Width, Frac, Signed};
        solver->reset();
        camada::SMTExprRef All;
        for (uint64_t Raw = 0; Raw < (uint64_t(1) << Width); ++Raw) {
          camada::SMTExprRef X = mkConst(solver, F, Raw);
          camada::SMTExprRef C = solver->mkAnd(
              solver->mkFXPEqual(
                  solver->mkFXPAbs(X),
                  mkConst(solver, F, refAbs(F, refDecode(F, Raw)))),
              solver->mkEqual(solver->mkFXPCountls(X, 8),
                              solver->mkBVFromDec(refCountls(F, Raw), 8)));
          All = All ? solver->mkAnd(All, C) : C;
        }
        solver->addConstraint(All);
        REQUIRE(solver->check() == camada::checkResult::SAT);
      }
    }
  }

  // The saturating case that distinguishes mkFXPAbs from the obvious
  // composition: in s.7, abs(-1.0) is not representable, so it clamps to
  // the maximum instead of wrapping back to the minimum.
  {
    solver->reset();
    RefFormat F{8, 7, true};
    solver->addConstraint(solver->mkFXPEqual(
        solver->mkFXPAbs(mkConst(solver, F, 0x80)), mkConst(solver, F, 0x7f)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Symbolic properties at a width no host sweep reaches: shifting left
  // by the sign-copy count never changes the sign, and abs is idempotent.
  {
    solver->reset();
    camada::SMTSortRef Wide = solver->mkFXPSort(40, 20, true);
    camada::SMTExprRef X = solver->mkSymbol("fxp_cls_x", Wide);
    camada::SMTExprRef A = solver->mkFXPAbs(X);
    camada::SMTExprRef Idem = solver->mkFXPEqual(solver->mkFXPAbs(A), A);
    // Count fits in the format width, so 8 bits is ample for 40.
    camada::SMTExprRef N = solver->mkFXPCountls(X, 8);
    camada::SMTExprRef InRange = solver->mkBVUle(N, solver->mkBVFromDec(39, 8));
    solver->addConstraint(solver->mkNot(solver->mkAnd(Idem, InRange)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }
}

// Correctly-rounded square root: the reference is exact integer
// arithmetic (the unique r with r*r <= raw*2^n < (r+1)*(r+1)), not any
// library's approximation — see mkFXPSqrt's contract.
// Correctly-rounded exp for the two 16-bit _Accum formats. `long double`
// carries a 64-bit mantissa, far more than the ~24 bits these formats can
// resolve, so rounding the host result is exact for every input here —
// the wider formats are covered by the offline checks against arbitrary
// precision instead (see scripts/fxp_exp_bounds.txt).
inline uint64_t refExp(const RefFormat &F, int64_t Raw) {
  long double X = (long double)Raw / (long double)(uint64_t(1) << F.FracBits);
  long double V = expl(X) * (long double)(uint64_t(1) << F.FracBits);
  long double MaxV = (long double)F.maxRaw();
  if (!(V < MaxV + 0.5L))
    return (uint64_t)F.maxRaw();
  long double Fl = floorl(V);
  long double Frac = V - Fl;
  uint64_t Q = (uint64_t)Fl;
  if (Frac > 0.5L || (Frac == 0.5L && (Q & 1)))
    ++Q;
  return std::min<uint64_t>(Q, (uint64_t)F.maxRaw());
}

// Per-backend check: a handful of vectors spanning the underflow tail,
// the ordinary range and saturation. The exhaustive comparison against
// every input of both 16-bit formats is far too heavy to repeat on seven
// backends (~130s each) and lives in a single dedicated test case
// instead; the encoding is common-layer, so one backend proves it.
inline void fxp_exp_semantics(const camada::SMTSolverRef &solver) {
  for (const RefFormat &F : {RefFormat{16, 7, true}, RefFormat{16, 8, false}}) {
    solver->reset();
    camada::SMTExprRef All;
    const int64_t Probes[] = {0,   1,    -1,  64,   -64,  128, -128,
                              256, -256, 700, -700, -798, 900, -1200};
    for (int64_t In : Probes) {
      if (!F.IsSigned && In < 0)
        continue;
      uint64_t Raw = refWrap(F, In);
      camada::SMTExprRef C =
          solver->mkFXPEqual(solver->mkFXPExp(mkConst(solver, F, Raw)),
                             mkConst(solver, F, refExp(F, refDecode(F, Raw))));
      All = All ? solver->mkAnd(All, C) : C;
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }
}

// Every input of both 16-bit _Accum formats, against the host reference.
// One backend only: see fxp_exp_semantics.
inline void fxp_exp_exhaustive(const camada::SMTSolverRef &solver) {
  // Only the band where exp() is neither 0 nor saturated is enumerated.
  // Every input outside it has the same answer and reaches it through the
  // same two comparisons, so sweeping the other ~63000 spends minutes
  // re-testing one branch. The real bands are ~1400 inputs wide (see
  // scripts/fxp_exp_bounds.txt); this walks a generous superset, and the
  // per-backend fixture probes the tails either side.
  for (const RefFormat &F : {RefFormat{16, 7, true}, RefFormat{16, 8, false}}) {
    const int64_t Lo = F.IsSigned ? -900 : 0;
    const int64_t Hi = 1500;
    for (int64_t Base = Lo; Base <= Hi; Base += 1024) {
      solver->reset();
      camada::SMTExprRef All;
      for (int64_t I = Base; I < Base + 1024 && I <= Hi; ++I) {
        uint64_t Raw = refWrap(F, I);
        camada::SMTExprRef C = solver->mkFXPEqual(
            solver->mkFXPExp(mkConst(solver, F, Raw)),
            mkConst(solver, F, refExp(F, refDecode(F, Raw))));
        All = All ? solver->mkAnd(All, C) : C;
      }
      solver->addConstraint(All);
      REQUIRE(solver->check() == camada::checkResult::SAT);
    }
  }

  // The saturating and underflowing tails, sampled across their whole
  // extent rather than assumed uniform: an early version of the encoding
  // overflowed the 2^k shift and wrapped to a value that then passed the
  // range check, and it did so only for large inputs (x = 47.75 in s8.7,
  // raw 6112) well beyond the band swept above.
  for (const RefFormat &F : {RefFormat{16, 7, true}, RefFormat{16, 8, false}}) {
    solver->reset();
    camada::SMTExprRef All;
    const int64_t Step = 37; // coprime with the format widths
    for (int64_t I = F.minRaw(); I <= F.maxRaw(); I += Step) {
      uint64_t Raw = refWrap(F, I);
      camada::SMTExprRef C =
          solver->mkFXPEqual(solver->mkFXPExp(mkConst(solver, F, Raw)),
                             mkConst(solver, F, refExp(F, refDecode(F, Raw))));
      All = All ? solver->mkAnd(All, C) : C;
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // The wider formats are spot-checked; their exhaustive comparison
  // against arbitrary-precision arithmetic runs offline.
  {
    solver->reset();
    RefFormat F{32, 15, true};
    camada::SMTExprRef All;
    const std::pair<int64_t, uint64_t> V[] = {
        {0, 32768}, {32768, 89073}, {-32768, 12055}, {1000000, 2147483647}};
    for (auto [In, Out] : V) {
      uint64_t InBits = uint64_t(In) & ((uint64_t(1) << F.Width) - 1);
      camada::SMTExprRef C =
          solver->mkFXPEqual(solver->mkFXPExp(mkConst(solver, F, InBits)),
                             mkConst(solver, F, Out));
      All = All ? solver->mkAnd(All, C) : C;
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }
}

// Correctly-rounded fixed-point square root: nearest, ties to even.
// The loop yields the floor and leaves N as the remainder S - R*R, and
// the true root exceeds the midpoint exactly when that remainder is
// greater than R, since (R + 1/2)^2 = R*R + R + 1/4.
inline uint64_t refSqrt(const RefFormat &F, uint64_t Raw) {
  const uint64_t S = Raw << F.FracBits;
  uint64_t N = S;
  uint64_t R = 0, Bit = uint64_t(1) << 62;
  while (Bit > N)
    Bit >>= 2;
  while (Bit) {
    if (N >= R + Bit) {
      N -= R + Bit;
      R = (R >> 1) + Bit;
    } else
      R >>= 1;
    Bit >>= 2;
  }
  const uint64_t Rem = S - R * R;
  if (Rem > R || (Rem == R && (R & 1)))
    ++R;
  return R;
}

inline void fxp_sqrt_semantics(const camada::SMTSolverRef &solver) {
  // Exhaustive over every format up to 8 bits, every non-negative value.
  for (unsigned Width = 2; Width <= 8; ++Width) {
    for (unsigned Frac = 0; Frac <= Width; ++Frac) {
      for (bool Signed : {true, false}) {
        if (Signed && Frac >= Width)
          continue;
        RefFormat F{Width, Frac, Signed};
        solver->reset();
        camada::SMTExprRef All;
        for (uint64_t Raw = 0; Raw <= uint64_t(F.maxRaw()); ++Raw) {
          camada::SMTExprRef C =
              solver->mkFXPEqual(solver->mkFXPSqrt(mkConst(solver, F, Raw)),
                                 mkConst(solver, F, refSqrt(F, Raw)));
          All = All ? solver->mkAnd(All, C) : C;
        }
        solver->addConstraint(All);
        REQUIRE(solver->check() == camada::checkResult::SAT);
      }
    }
  }

  // The defining property, proved over ALL symbolic values rather than
  // enumerated. Correct rounding to nearest means the true root lies
  // within half an ulp of r, i.e. between the two midpoints:
  //
  //     (2r - 1)^2 <= 4*x + 1   and   4*x <= (2r + 1)^2
  //
  // at the format's scale. The `+ 1` on the lower bound matters: a tie
  // rounded UP sits exactly one below (2r-1)^2, since 4*x is an integer
  // and the midpoint squared is not. Ties satisfy both bounds either
  // way, so this admits both directions; the exhaustive loop above is
  // what pins ties-to-even.
  {
    solver->reset();
    unsigned W = 12, N = 6, Wide = 2 * (W + N) + 6;
    camada::SMTSortRef F = solver->mkFXPSort(W, N, true);
    camada::SMTExprRef X = solver->mkSymbol("fxp_sqrt_x", F);
    camada::SMTExprRef R = solver->mkFXPSqrt(X);
    auto ext = [&](const camada::SMTExprRef &E) {
      return solver->mkBVZeroExt(Wide - W, solver->mkFXPToRawBV(E));
    };
    camada::SMTExprRef Rx = ext(R), Xx = ext(X);
    camada::SMTExprRef Two = solver->mkBVFromDec(2, Wide);
    camada::SMTExprRef One = solver->mkBVFromDec(1, Wide);
    camada::SMTExprRef Xs = solver->mkBVShl(Xx, solver->mkBVFromDec(N, Wide));
    camada::SMTExprRef FourX = solver->mkBVShl(Xs, Two);
    camada::SMTExprRef TwoR = solver->mkBVMul(Rx, Two);
    camada::SMTExprRef Lo = solver->mkBVSub(TwoR, One);
    camada::SMTExprRef Hi = solver->mkBVAdd(TwoR, One);
    // r == 0 has no lower midpoint; the lower bound is vacuous there.
    camada::SMTExprRef RIsZero =
        solver->mkEqual(Rx, solver->mkBVFromDec(0, Wide));
    camada::SMTExprRef LoOk =
        solver->mkOr(RIsZero, solver->mkBVUle(solver->mkBVMul(Lo, Lo),
                                              solver->mkBVAdd(FourX, One)));
    camada::SMTExprRef Holds =
        solver->mkAnd(LoOk, solver->mkBVUle(FourX, solver->mkBVMul(Hi, Hi)));
    camada::SMTExprRef NonNeg = solver->mkNot(solver->mkFXPLt(
        X, solver->mkFXPFromBin(refBits(RefFormat{W, N, true}, 0),
                                solver->mkFXPSort(W, N, true))));
    solver->addConstraint(solver->mkAnd(NonNeg, solver->mkNot(Holds)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }

  // Negative operands: the result is pinned to zero rather than left as
  // whatever the two's-complement bits happen to encode, so a consumer
  // who omits the `x < 0` guard sees an obviously wrong answer instead of
  // a plausible negative one (sqrt(-1.0) would otherwise read as -1.0).
  {
    solver->reset();
    RefFormat F{8, 7, true};
    camada::SMTExprRef All;
    for (uint64_t Raw : {uint64_t(0x80), uint64_t(0xC0), uint64_t(0xFF)}) {
      camada::SMTExprRef C = solver->mkFXPEqual(
          solver->mkFXPSqrt(mkConst(solver, F, Raw)), mkConst(solver, F, 0));
      All = All ? solver->mkAnd(All, C) : C;
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }
}

inline void fxp_round_semantics(const camada::SMTSolverRef &solver) {
  // Exhaustive over every 5- and 6-bit format, every digit count, both
  // signednesses, and all three tie rules: small enough to enumerate
  // every raw value, wide enough to exercise saturation, ties, and
  // negative rounding.
  for (camada::FXPRM Tie : {camada::FXPRM::NearestTiesTowardPositive,
                            camada::FXPRM::NearestTiesAwayFromZero,
                            camada::FXPRM::NearestTiesToEven}) {
    for (unsigned Width : {5u, 6u}) {
      for (unsigned Frac = 0; Frac < Width; ++Frac) {
        for (bool Signed : {true, false}) {
          if (Signed && Frac + 1 > Width - 1)
            continue; // signed needs a non-fraction sign bit
          RefFormat F{Width, Frac, Signed};
          for (unsigned Digits = 0; Digits <= Frac + 1; ++Digits) {
            solver->reset();
            camada::SMTExprRef All;
            for (uint64_t Raw = 0; Raw < (uint64_t(1) << Width); ++Raw) {
              camada::SMTExprRef C = solver->mkFXPEqual(
                  solver->mkFXPRound(mkConst(solver, F, Raw), Digits, Tie),
                  mkConst(solver, F,
                          refRound(F, refDecode(F, Raw), Digits, Tie)));
              All = All ? solver->mkAnd(All, C) : C;
            }
            solver->addConstraint(All);
            REQUIRE(solver->check() == camada::checkResult::SAT);
          }
        }
      }
    }
  }

  // The three rules are pairwise distinguishable, which is the point of
  // exposing the choice. In s.4 at zero digits: -0.5 (raw -8) stays at 0
  // toward positive but goes to -1.0 away from zero, and +0.5 (raw 8)
  // goes to 1.0 under both of those but down to 0 under ties-to-even,
  // whose neighbour 0 is the one with a zero in the last kept bit.
  {
    solver->reset();
    RefFormat F{6, 4, true};
    auto R = [&](int64_t Raw, unsigned D, camada::FXPRM T) {
      return solver->mkFXPRound(mkConst(solver, F, refWrap(F, Raw)), D, T);
    };
    auto C = [&](int64_t Raw) { return mkConst(solver, F, refWrap(F, Raw)); };
    using camada::FXPRM;
    camada::SMTExprRef All = solver->mkAnd(
        solver->mkFXPEqual(R(-8, 0, FXPRM::NearestTiesTowardPositive), C(0)),
        solver->mkFXPEqual(R(-8, 0, FXPRM::NearestTiesAwayFromZero), C(-16)));
    All = solver->mkAnd(
        All, solver->mkFXPEqual(R(-8, 0, FXPRM::NearestTiesToEven), C(0)));
    All = solver->mkAnd(
        All,
        solver->mkAnd(solver->mkFXPEqual(
                          R(8, 0, FXPRM::NearestTiesTowardPositive), C(16)),
                      solver->mkFXPEqual(
                          R(8, 0, FXPRM::NearestTiesAwayFromZero), C(16))));
    All = solver->mkAnd(
        All, solver->mkFXPEqual(R(8, 0, FXPRM::NearestTiesToEven), C(0)));
    // The directed modes never consult the halfway point: 0.5 (raw 8) and
    // 0.75 (raw 12) round the same way under each, and -0.5 (raw -8)
    // separates floor from truncate.
    for (int64_t Raw : {int64_t(8), int64_t(12)}) {
      All = solver->mkAnd(
          All, solver->mkFXPEqual(R(Raw, 0, FXPRM::TowardZero), C(0)));
      All = solver->mkAnd(
          All, solver->mkFXPEqual(R(Raw, 0, FXPRM::TowardNegative), C(0)));
      All = solver->mkAnd(
          All, solver->mkFXPEqual(R(Raw, 0, FXPRM::TowardPositive), C(16)));
    }
    // Negative: truncate goes toward zero, floor goes away from it.
    All = solver->mkAnd(All,
                        solver->mkFXPEqual(R(-8, 0, FXPRM::TowardZero), C(0)));
    All = solver->mkAnd(
        All, solver->mkFXPEqual(R(-8, 0, FXPRM::TowardNegative), C(-16)));
    All = solver->mkAnd(
        All, solver->mkFXPEqual(R(-8, 0, FXPRM::TowardPositive), C(0)));
    // Exact values are unchanged by every mode.
    for (camada::FXPRM M :
         {FXPRM::TowardZero, FXPRM::TowardNegative, FXPRM::TowardPositive})
      All = solver->mkAnd(All, solver->mkFXPEqual(R(16, 0, M), C(16)));
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // LLVM libc's own RoundTest vectors, on _Fract (s.15). EPS is one ulp.
  {
    solver->reset();
    RefFormat Fr{16, 15, true};
    const uint64_t Half = 1u << 14, Eps = 1, One = 0x7fff; // 1.0 saturates
    struct {
      uint64_t In;
      unsigned Digits;
      uint64_t Out;
    } V[] = {
        {0, 0, 0},                           // zero stays zero
        {Half, 0, One},                      // 0.5 -> 1 (ties up, saturating)
        {Half, 1, Half},                     // 0.5 kept at 1 digit
        {Half + Eps, 0, One},                // just above half rounds up
        {Half - Eps, 0, 0},                  // just below half rounds down
        {Eps, 15, Eps},                      // eps kept at full precision
        {Eps, 14, 2 * Eps},                  // eps at one fewer bit doubles
        {Eps, 13, 0},                        // eps at two fewer bits vanishes
        {refWrap(Fr, -int64_t(Half)), 0, 0}, // -0.5 -> 0 (ties to +inf)
        {refWrap(Fr, -int64_t(Half)), 1, refWrap(Fr, -int64_t(Half))},
        {refWrap(Fr, -int64_t(Half) - 1), 0, refWrap(Fr, -int64_t(One) - 1)},
    };
    camada::SMTExprRef All;
    for (auto &T : V) {
      camada::SMTExprRef C = solver->mkFXPEqual(
          solver->mkFXPRound(mkConst(solver, Fr, T.In), T.Digits,
                             camada::FXPRM::NearestTiesTowardPositive),
          mkConst(solver, Fr, T.Out));
      All = All ? solver->mkAnd(All, C) : C;
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Symbolic properties at a width no host sweep reaches: rounding to the
  // full fraction width is the identity, and every result either has its
  // discarded fraction bits clear or is the saturated maximum (whose low
  // bits are all ones, so the mask property genuinely does not hold
  // there).
  {
    solver->reset();
    camada::SMTSortRef Wide = solver->mkFXPSort(48, 31, true);
    camada::SMTExprRef X = solver->mkSymbol("fxp_round_x", Wide);
    camada::SMTExprRef Id = solver->mkFXPEqual(
        solver->mkFXPRound(X, 31, camada::FXPRM::NearestTiesTowardPositive), X);
    camada::SMTExprRef R =
        solver->mkFXPRound(X, 23, camada::FXPRM::NearestTiesTowardPositive);
    camada::SMTExprRef Max = solver->mkFXPFromBin(
        refBits(RefFormat{48, 31, true},
                uint64_t(RefFormat{48, 31, true}.maxRaw())),
        Wide);
    camada::SMTExprRef Low = solver->mkOr(
        solver->mkEqual(solver->mkBVExtract(7, 0, solver->mkFXPToRawBV(R)),
                        solver->mkBVFromDec(0, 8)),
        solver->mkFXPEqual(R, Max));
    solver->addConstraint(solver->mkNot(solver->mkAnd(Id, Low)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }
}

// Fixed <-> floating point: targeted cases the oracle tables cannot carry
// (a nonstandard FP target, predicate boundaries, a symbolic round-trip).
// The oracle fixture in fxporacle.test.h pins the full float/double
// semantics; these pin the parts C programs never reach.
inline void fxp_fp_conversion_semantics(const camada::SMTSolverRef &solver,
                                        camada::FPEncoding Enc) {
  // Single-rounding discriminator: s(32,30) raw 49185 (= 49185 * 2^-30)
  // converts into binary16's subnormal range. Rounding the exact value
  // once gives frac 769 (0x0301); converting to binary16 first and
  // scaling afterwards rounds twice (49185 -> 49184, then a tie to even
  // downwards) and gives 0x0300. This is the case that makes the
  // conversion camada-owned instead of consumer-composed. BV encoding
  // only: not every backend has a native binary16 (cvc5's default build
  // stops at Float32/Float64).
  if (Enc == camada::FPEncoding::BV) {
    solver->reset();
    camada::SMTSortRef Fmt = solver->mkFXPSort(32, 30, true);
    camada::SMTSortRef Half = solver->mkFPSort(5, 10, Enc);
    camada::SMTExprRef X =
        solver->mkFXPFromBin(refBits(RefFormat{32, 30, true}, 49185), Fmt);
    camada::SMTExprRef R =
        solver->mkFXPToFP(X, Half, camada::RM::ROUND_TO_EVEN);
    solver->addConstraint(solver->mkEqual(solver->mkIEEEFPToBV(R),
                                          solver->mkBVFromDec(0x0301, 16)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Overflow predicate boundaries and the toward-zero direction, s.15
  // target from binary32 sources.
  {
    solver->reset();
    camada::SMTSortRef To = solver->mkFXPSort(16, 15, true);
    auto fp32 = [&](uint32_t Bits) {
      return solver->mkFPFromBin(refBits(RefFormat{32, 0, false}, Bits), 8,
                                 Enc);
    };
    // Defined iff the toward-zero result fits (Clang lowers the plain
    // conversion as fmul-by-2^n + fptosi): the rails themselves — max =
    // 32767/32768 (0x3f7ffe00), min = -1.0 (0xbf800000) — and even one
    // ulp beyond them (0x3f7ffe01, 0xbf800001), which still truncates
    // into range.
    camada::SMTExprRef Ok = solver->mkBool(true);
    for (uint32_t Good : {0x3f7ffe00u, 0xbf800000u, 0x3f7ffe01u, 0xbf800001u})
      Ok = solver->mkAnd(Ok, solver->mkNot(solver->mkFPToFXPOverflow(
                                 fp32(Good), To, camada::FXPRM::TowardZero)));
    // Undefined: values whose truncation falls outside (1.0 scales to
    // 32768, -1.000030518 to -32769), NaN, and +-infinity.
    for (uint32_t Bad :
         {0x3f800000u, 0xbf800100u, 0x7fc00000u, 0x7f800000u, 0xff800000u})
      Ok = solver->mkAnd(Ok, solver->mkFPToFXPOverflow(
                                 fp32(Bad), To, camada::FXPRM::TowardZero));
    // Toward zero, not floor: -0.7f scales to -22937.6, truncating to
    // -22937 (raw 0xa667); flooring would give -22938.
    Ok = solver->mkAnd(
        Ok,
        solver->mkFXPEqual(
            solver->mkFPToFXP(fp32(0xbf333333), To, camada::FXPRM::TowardZero),
            solver->mkFXPFromBin(refBits(RefFormat{16, 15, true}, 0xa667),
                                 To)));
    solver->addConstraint(Ok);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Oracle-pinned vectors on the standard formats, run under BOTH
  // encodings (the kToFP/kFromFP tables themselves run BV-only). These
  // are the rows that discriminate the rounding rules: RNE ties in both
  // directions and the all-ones carry-out for fixed->float, the rails
  // and NaN for saturating float->fixed.
  {
    solver->reset();
    camada::SMTSortRef L31 = solver->mkFXPSort(32, 31, true);
    camada::SMTSortRef F32 = solver->mkFP32Sort(Enc);
    camada::SMTExprRef Ok = solver->mkBool(true);
    // (raw of long _Fract, expected binary32 bits) straight from kToFP.
    const std::pair<uint32_t, uint32_t> ToFP32[] = {
        {0x2AAAAAAB, 0x3eaaaaab}, // tail above half rounds up
        {0x40000040, 0x3f000000}, // exact tie, keep even
        {0x400000C0, 0x3f000002}, // exact tie, round up to even
        {0x40000140, 0x3f000002}, // exact tie, keep even
        {0x7FFFFFC0, 0x3f800000}, // tie at all-ones carries out to 1.0
    };
    for (auto [Raw, Bits] : ToFP32) {
      camada::SMTExprRef X =
          solver->mkFXPFromBin(refBits(RefFormat{32, 31, true}, Raw), L31);
      Ok = solver->mkAnd(
          Ok, solver->mkEqual(solver->mkIEEEFPToBV(solver->mkFXPToFP(
                                  X, F32, camada::RM::ROUND_TO_EVEN)),
                              solver->mkBVFromBin(
                                  refBits(RefFormat{32, 0, false}, Bits), 32)));
    }
    // long _Accum -> double at the 53-bit boundary: tail below half
    // rounds down.
    camada::SMTSortRef L31A = solver->mkFXPSort(64, 31, true);
    camada::SMTExprRef Y = solver->mkFXPFromBin(
        refBits(RefFormat{64, 31, true}, 0x4000000000000180ull), L31A);
    Ok = solver->mkAnd(
        Ok,
        solver->mkEqual(
            solver->mkIEEEFPToBV(solver->mkFXPToFP(Y, solver->mkFP64Sort(Enc),
                                                   camada::RM::ROUND_TO_EVEN)),
            solver->mkBVFromBin(
                refBits(RefFormat{64, 0, false}, 0x41e0000000000000ull), 64)));
    // Saturating float->fixed: rails, infinities, and NaN -> 0.
    camada::SMTSortRef S15 = solver->mkFXPSort(16, 15, true);
    const std::pair<uint32_t, uint32_t> FromFP32[] = {
        {0x40200000, 0x7fff}, // 2.5 clamps to max
        {0xc0200000, 0x8000}, // -2.5 clamps to min
        {0x7f800000, 0x7fff}, // +inf
        {0xff800000, 0x8000}, // -inf
        {0x7fc00000, 0x0000}, // NaN -> 0
        {0xbf333333, 0xa667}, // -0.7 truncates toward zero
    };
    for (auto [Bits, Raw] : FromFP32) {
      camada::SMTExprRef F =
          solver->mkFPFromBin(refBits(RefFormat{32, 0, false}, Bits), 8, Enc);
      Ok = solver->mkAnd(
          Ok, solver->mkFXPEqual(
                  solver->mkFPToFXPSat(F, S15, camada::FXPRM::TowardZero),
                  solver->mkFXPFromBin(refBits(RefFormat{16, 15, true}, Raw),
                                       S15)));
    }
    solver->addConstraint(Ok);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Symbolic round-trip: every s.7 value is exactly representable in
  // binary32, so converting there and back is the identity and the
  // overflow predicate never fires (proved UNSAT over a symbolic value).
  {
    solver->reset();
    camada::SMTSortRef Fmt = solver->mkFXPSort(8, 7, true);
    camada::SMTSortRef F32 = solver->mkFP32Sort(Enc);
    camada::SMTExprRef X = solver->mkSymbol("fxp_rt_x", Fmt);
    camada::SMTExprRef F = solver->mkFXPToFP(X, F32, camada::RM::ROUND_TO_EVEN);
    solver->addConstraint(solver->mkOr(
        solver->mkNot(solver->mkFXPEqual(
            solver->mkFPToFXP(F, Fmt, camada::FXPRM::TowardZero), X)),
        solver->mkFPToFXPOverflow(F, Fmt, camada::FXPRM::TowardZero)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }
}

} // namespace camada_fxp_test

// The fixtures are referenced unqualified from tests.h and the per-backend
// pipeline test files.
using camada_fxp_test::fxp_abs_countls_semantics;
using camada_fxp_test::fxp_boundary_overflow_semantics;
using camada_fxp_test::fxp_conversion_matrix;
using camada_fxp_test::fxp_exhaustive_semantics;
using camada_fxp_test::fxp_exp_exhaustive;
using camada_fxp_test::fxp_exp_semantics;
using camada_fxp_test::fxp_fp_conversion_semantics;
using camada_fxp_test::fxp_mixed_format_semantics;
using camada_fxp_test::fxp_model_and_constructs;
using camada_fxp_test::fxp_round_semantics;
using camada_fxp_test::fxp_rounding_semantics;
using camada_fxp_test::fxp_sat_conversion_semantics;
using camada_fxp_test::fxp_sat_exhaustive_semantics;
using camada_fxp_test::fxp_sat_shift_semantics;
using camada_fxp_test::fxp_shift_semantics;
using camada_fxp_test::fxp_sqrt_semantics;
using camada_fxp_test::fxp_symbolic_shift_semantics;

#endif // CAMADA_REGRESSION_FXP_TEST_H_
