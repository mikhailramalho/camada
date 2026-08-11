// Conformance of every bit-vector operation against SMT-LIB semantics, on
// every backend.
//
// This exists because `bvsrem` returned the wrong sign on STP for five
// years: the backend called STP's modulo routine, whose result takes the
// sign of the divisor rather than the dividend, and the two agree
// whenever the operand signs match. Nothing caught it because no fixture
// had ever called mkBVSRem — and it was one of a dozen operations in the
// same position.
//
// So the check is exhaustive rather than sampled: every operation is
// evaluated over all operand pairs of a 4-bit sort (and every shift
// amount, including the out-of-range ones), against a host model written
// from the SMT-LIB definitions. A backend that disagrees on any single
// pair fails, which is the only way to catch a convention mismatch that
// happens to agree on the obvious inputs.

#ifndef CAMADA_REGRESSION_BVCONFORMANCE_TEST_H_
#define CAMADA_REGRESSION_BVCONFORMANCE_TEST_H_

#include "camada.h"

#include <catch2/catch_test_macros.hpp>

#include <cstdint>
#include <string>

namespace camada_bv_conformance {

constexpr unsigned BVW = 4;
constexpr unsigned BVN = 1u << BVW;

inline std::string bvBits(uint64_t V, unsigned W = BVW) {
  std::string B(W, '0');
  for (unsigned I = 0; I < W; ++I)
    if ((V >> I) & 1)
      B[W - 1 - I] = '1';
  return B;
}

inline int64_t sval(uint64_t V) {
  return (V >> (BVW - 1)) ? (int64_t)V - (int64_t)BVN : (int64_t)V;
}

inline uint64_t mask(uint64_t V) { return V & (BVN - 1); }

// --- SMT-LIB reference semantics -------------------------------------------
// Division and remainder follow SMT-LIB: bvudiv/bvurem by zero return
// all-ones and the dividend respectively; bvsdiv truncates toward zero
// and bvsrem takes the sign of the DIVIDEND (unlike a modulo, which takes
// the divisor's).

inline uint64_t refUDiv(uint64_t A, uint64_t B) {
  return B == 0 ? BVN - 1 : A / B;
}

inline uint64_t refURem(uint64_t A, uint64_t B) { return B == 0 ? A : A % B; }

inline uint64_t refSDiv(uint64_t A, uint64_t B) {
  if (B == 0)
    return sval(A) >= 0 ? BVN - 1 : 1;
  int64_t Q = sval(A) / sval(B); // C++ truncates toward zero, as SMT-LIB does
  return mask((uint64_t)Q);
}

inline uint64_t refSRem(uint64_t A, uint64_t B) {
  if (B == 0)
    return A;
  int64_t R = sval(A) % sval(B); // sign of the dividend
  return mask((uint64_t)R);
}

inline uint64_t refShl(uint64_t A, uint64_t S) {
  return S >= BVW ? 0 : mask(A << S);
}

inline uint64_t refLshr(uint64_t A, uint64_t S) {
  return S >= BVW ? 0 : A >> S;
}

inline uint64_t refAshr(uint64_t A, uint64_t S) {
  bool Neg = (A >> (BVW - 1)) != 0;
  if (S >= BVW)
    return Neg ? BVN - 1 : 0;
  uint64_t R = A >> S;
  if (Neg)
    R |= mask(~((BVN - 1) >> S));
  return R;
}

// --- The fixture -----------------------------------------------------------

inline void bv_conformance_semantics(const camada::SMTSolverRef &solver) {
  auto C = [&](uint64_t V) {
    return solver->mkBVFromBin(bvBits(V), solver->mkBVSort(BVW));
  };
  auto B = [&](bool V) { return solver->mkBool(V); };

  // Binary value-producing operations, over every operand pair.
  {
    solver->reset();
    camada::SMTExprRef All = solver->mkBool(true);
    for (uint64_t A = 0; A < BVN; ++A) {
      for (uint64_t D = 0; D < BVN; ++D) {
        auto eq = [&](const camada::SMTExprRef &E, uint64_t Want) {
          All = solver->mkAnd(All, solver->mkEqual(E, C(Want)));
        };
        eq(solver->mkBVAdd(C(A), C(D)), mask(A + D));
        eq(solver->mkBVSub(C(A), C(D)), mask(A - D));
        eq(solver->mkBVMul(C(A), C(D)), mask(A * D));
        eq(solver->mkBVAnd(C(A), C(D)), A & D);
        eq(solver->mkBVOr(C(A), C(D)), A | D);
        eq(solver->mkBVXor(C(A), C(D)), A ^ D);
        eq(solver->mkBVNand(C(A), C(D)), mask(~(A & D)));
        eq(solver->mkBVNor(C(A), C(D)), mask(~(A | D)));
        eq(solver->mkBVXnor(C(A), C(D)), mask(~(A ^ D)));
        eq(solver->mkBVUDiv(C(A), C(D)), refUDiv(A, D));
        eq(solver->mkBVURem(C(A), C(D)), refURem(A, D));
        eq(solver->mkBVSDiv(C(A), C(D)), refSDiv(A, D));
        eq(solver->mkBVSRem(C(A), C(D)), refSRem(A, D));
        eq(solver->mkBVShl(C(A), C(D)), refShl(A, D));
        eq(solver->mkBVLshr(C(A), C(D)), refLshr(A, D));
        eq(solver->mkBVAshr(C(A), C(D)), refAshr(A, D));
      }
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Comparisons, over every operand pair.
  {
    solver->reset();
    camada::SMTExprRef All = solver->mkBool(true);
    for (uint64_t A = 0; A < BVN; ++A) {
      for (uint64_t D = 0; D < BVN; ++D) {
        auto eq = [&](const camada::SMTExprRef &E, bool Want) {
          All = solver->mkAnd(All, solver->mkEqual(E, B(Want)));
        };
        eq(solver->mkBVUlt(C(A), C(D)), A < D);
        eq(solver->mkBVUle(C(A), C(D)), A <= D);
        eq(solver->mkBVUgt(C(A), C(D)), A > D);
        eq(solver->mkBVUge(C(A), C(D)), A >= D);
        eq(solver->mkBVSlt(C(A), C(D)), sval(A) < sval(D));
        eq(solver->mkBVSle(C(A), C(D)), sval(A) <= sval(D));
        eq(solver->mkBVSgt(C(A), C(D)), sval(A) > sval(D));
        eq(solver->mkBVSge(C(A), C(D)), sval(A) >= sval(D));
      }
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Unary operations and the width-changing ones, over every value.
  {
    solver->reset();
    camada::SMTExprRef All = solver->mkBool(true);
    for (uint64_t A = 0; A < BVN; ++A) {
      All = solver->mkAnd(
          All, solver->mkEqual(solver->mkBVNeg(C(A)), C(mask(0 - A))));
      All = solver->mkAnd(All,
                          solver->mkEqual(solver->mkBVNot(C(A)), C(mask(~A))));
      // Reductions are one-bit results: RedOr is "any bit set", RedAnd is
      // "all bits set".
      All = solver->mkAnd(
          All, solver->mkEqual(solver->mkBVRedOr(C(A)),
                               solver->mkBVFromBin(bvBits(A != 0, 1),
                                                   solver->mkBVSort(1))));
      All = solver->mkAnd(
          All, solver->mkEqual(solver->mkBVRedAnd(C(A)),
                               solver->mkBVFromBin(bvBits(A == BVN - 1, 1),
                                                   solver->mkBVSort(1))));
      // Extensions preserve the value under their own signedness.
      All = solver->mkAnd(
          All, solver->mkEqual(
                   solver->mkBVZeroExt(4, C(A)),
                   solver->mkBVFromBin(bvBits(A, 8), solver->mkBVSort(8))));
      All = solver->mkAnd(
          All, solver->mkEqual(
                   solver->mkBVSignExt(4, C(A)),
                   solver->mkBVFromBin(bvBits((uint64_t)sval(A) & 0xff, 8),
                                       solver->mkBVSort(8))));
      // Extract of the whole width is the identity; concat doubles it.
      All = solver->mkAnd(
          All, solver->mkEqual(solver->mkBVExtract(BVW - 1, 0, C(A)), C(A)));
      All = solver->mkAnd(
          All, solver->mkEqual(solver->mkBVConcat(C(A), C(A)),
                               solver->mkBVFromBin(bvBits(A * 17, 8),
                                                   solver->mkBVSort(8))));
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Overflow predicates, over every operand pair. Each is true exactly
  // when the exact result leaves the representable range.
  {
    solver->reset();
    camada::SMTExprRef All = solver->mkBool(true);
    const int64_t SMin = -(int64_t)(BVN / 2), SMax = (int64_t)(BVN / 2) - 1;
    for (uint64_t A = 0; A < BVN; ++A) {
      for (uint64_t D = 0; D < BVN; ++D) {
        auto eq = [&](const camada::SMTExprRef &E, bool Want) {
          All = solver->mkAnd(All, solver->mkEqual(E, B(Want)));
        };
        eq(solver->mkBVUAddOverflow(C(A), C(D)), A + D >= BVN);
        eq(solver->mkBVUSubOverflow(C(A), C(D)), A < D);
        eq(solver->mkBVUMulOverflow(C(A), C(D)), A * D >= BVN);
        eq(solver->mkBVSAddOverflow(C(A), C(D)),
           sval(A) + sval(D) > SMax || sval(A) + sval(D) < SMin);
        eq(solver->mkBVSSubOverflow(C(A), C(D)),
           sval(A) - sval(D) > SMax || sval(A) - sval(D) < SMin);
        eq(solver->mkBVSMulOverflow(C(A), C(D)),
           sval(A) * sval(D) > SMax || sval(A) * sval(D) < SMin);
        // Signed division overflows only at MIN / -1.
        eq(solver->mkBVSDivOverflow(C(A), C(D)),
           sval(A) == SMin && sval(D) == -1);
      }
      // Negation overflows only at the signed minimum.
      All = solver->mkAnd(All, solver->mkEqual(solver->mkBVNegOverflow(C(A)),
                                               B(sval(A) == SMin)));
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }
}

} // namespace camada_bv_conformance

using camada_bv_conformance::bv_conformance_semantics;

#endif // CAMADA_REGRESSION_BVCONFORMANCE_TEST_H_
