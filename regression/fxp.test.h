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

#include <cassert>
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
            Value = solver->mkFXPMul(EA, EB);
            Pred = solver->mkFXPMulOverflow(EA, EB);
            break;
          case Op::Div:
            Ref = refDiv(F, A, B);
            Value = solver->mkFXPDiv(EA, EB);
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
    solver->addConstraint(
        solver->mkFXPEqual(solver->mkFXPMul(A, B), mkConst(solver, F, 127)));
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
  Conjuncts.push_back(
      solver->mkFXPEqual(solver->mkFXPDiv(C(-3), C(32)), C(-2)));
  // (3/16) / 2.0: exact raw quotient 1.5 -> raw 1.
  Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPDiv(C(3), C(32)), C(1)));
  // (-1/16) * (8/16): exact -0.5 raw; floor -> -1 raw (not 0).
  Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPMul(C(-1), C(8)), C(-1)));
  // ( 1/16) * (8/16): exact 0.5 raw; floor -> 0 raw.
  Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPMul(C(1), C(8)), C(0)));
  requireAllHold(solver, Conjuncts);

  // Fixed -> integer rounds toward zero: -1.5 -> -1 (a plain arithmetic
  // shift would floor to -2).
  solver->reset();
  camada::SMTExprRef MinusOneHalf = mkConst(solver, F, uint64_t(-24) & 0xFF);
  camada::SMTExprRef AsInt = solver->mkFXPToBV(MinusOneHalf, 8);
  solver->addConstraint(solver->mkEqual(AsInt, solver->mkBVFromDec(-1, 8)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Fixed -> fixed narrowing floors: -1.75 in Q3.4 (raw -28) into Q6.1 is
  // exactly -3.5 at one fraction bit, which floors to raw -4 = -2.0 — the
  // documented floor behavior, distinct from the toward-zero -3 = -1.5.
  solver->reset();
  camada::SMTExprRef MinusOneQ3 = mkConst(solver, F, uint64_t(-28) & 0xFF);
  RefFormat Narrow{8, 1, true};
  camada::SMTExprRef Converted =
      solver->mkFXPToFXP(MinusOneQ3, mkSort(solver, Narrow));
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
      Conjuncts.push_back(solver->mkNot(solver->mkFXPToFXPOverflow(V, ToSort)));
      // ...and is exact: converting up compares equal to the original
      // (mkFXPEqual scale-aligns across the two formats).
      Conjuncts.push_back(solver->mkFXPEqual(solver->mkFXPToFXP(V, ToSort), V));
    }
    requireAllHold(solver, Conjuncts);
  }

  // Signedness-changing narrow: unsigned 4.0 (raw 8 in U2.2) into signed
  // Q1.2 (max 3/4): overflow.
  {
    solver->reset();
    RefFormat U{4, 2, false}, S4{4, 2, true};
    camada::SMTExprRef V = mkConst(solver, U, 8);
    solver->addConstraint(solver->mkFXPToFXPOverflow(V, mkSort(solver, S4)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Negative into unsigned: overflow.
  {
    solver->reset();
    RefFormat S4{4, 2, true}, U{4, 2, false};
    camada::SMTExprRef V = mkConst(solver, S4, uint64_t(-1) & 0xF);
    solver->addConstraint(solver->mkFXPToFXPOverflow(V, mkSort(solver, U)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Wide formats (past 64 bits, 128-bit-plus intermediates): widening a
  // symbolic Q34.35 into Q69.70 is exact and overflow-free for all values.
  {
    solver->reset();
    camada::SMTSortRef WideSrc = solver->mkFXPSort(70, 35, true);
    camada::SMTSortRef WideDst = solver->mkFXPSort(140, 70, true);
    camada::SMTExprRef X = solver->mkSymbol("fxp_wide_x", WideSrc);
    solver->addConstraint(solver->mkFXPToFXPOverflow(X, WideDst));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
    solver->reset();
    WideSrc = solver->mkFXPSort(70, 35, true);
    WideDst = solver->mkFXPSort(140, 70, true);
    X = solver->mkSymbol("fxp_wide_x", WideSrc);
    solver->addConstraint(
        solver->mkNot(solver->mkFXPEqual(solver->mkFXPToFXP(X, WideDst), X)));
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
    camada::SMTExprRef Back = solver->mkFXPToBV(AsFXP, 8);
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
            Value = solver->mkFXPMulSat(EA, EB);
            break;
          case Op::Div:
            if (B == 0)
              continue;
            Ref = refDivSat(F, A, B);
            Value = solver->mkFXPDivSat(EA, EB);
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
        Conjuncts.push_back(
            solver->mkFXPEqual(solver->mkFXPToFXPSat(EA, mkSort(solver, To)),
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
              solver->mkEqual(solver->mkFXPToBVSat(EA, ToWidth, ToSigned),
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

} // namespace camada_fxp_test

// The fixtures are referenced unqualified from tests.h and the per-backend
// pipeline test files.
using camada_fxp_test::fxp_boundary_overflow_semantics;
using camada_fxp_test::fxp_conversion_matrix;
using camada_fxp_test::fxp_exhaustive_semantics;
using camada_fxp_test::fxp_mixed_format_semantics;
using camada_fxp_test::fxp_model_and_constructs;
using camada_fxp_test::fxp_rounding_semantics;
using camada_fxp_test::fxp_sat_conversion_semantics;
using camada_fxp_test::fxp_sat_exhaustive_semantics;
using camada_fxp_test::fxp_sat_shift_semantics;
using camada_fxp_test::fxp_shift_semantics;
using camada_fxp_test::fxp_symbolic_shift_semantics;

#endif // CAMADA_REGRESSION_FXP_TEST_H_
