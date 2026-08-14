// Conformance of the floating-point operations against IEEE-754, on every
// backend and under both encodings.
//
// Companion to bvconformance.test.h, written after the STP `bvsrem` bug
// showed what an untested operation can hide. The floating-point surface
// had thirteen operations no fixture called at all — every comparison
// operator, absolute value, format conversion, and the NaN and infinity
// constructors.
//
// Comparisons are the reason this matters more here than elsewhere. IEEE
// gives them semantics that look wrong until you know them: NaN compares
// false against everything including itself, so `x < y`, `x == y` and
// `x > y` are all false simultaneously; and +0 equals -0 despite having
// different bit patterns. A backend that reasons about comparisons as if
// they were a total order agrees with IEEE on every ordinary pair and
// disagrees only on those, which is exactly the shape of defect sampling
// misses.
//
// Every check runs under both FPEncoding::Native and FPEncoding::BV, so
// it also pins that camada's own bit-blasted encoding agrees with the
// backend's native one.

#ifndef CAMADA_REGRESSION_FPCONFORMANCE_TEST_H_
#define CAMADA_REGRESSION_FPCONFORMANCE_TEST_H_

#include "camada.h"

#include <catch2/catch_test_macros.hpp>

#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace camada_fp_conformance {

// A spread of float values covering the cases IEEE treats specially,
// alongside ordinary ones: both zeros, both infinities, a NaN, the
// smallest subnormal, and values either side of zero.
inline std::vector<float> conformanceValues() {
  return {0.0f,
          -0.0f,
          1.0f,
          -1.0f,
          2.5f,
          -2.5f,
          0.5f,
          -0.5f,
          std::numeric_limits<float>::infinity(),
          -std::numeric_limits<float>::infinity(),
          std::numeric_limits<float>::quiet_NaN(),
          std::numeric_limits<float>::denorm_min(),
          -std::numeric_limits<float>::denorm_min(),
          std::numeric_limits<float>::max(),
          std::numeric_limits<float>::lowest()};
}

inline std::string floatBits(float F) {
  uint32_t U;
  std::memcpy(&U, &F, sizeof U);
  std::string B(32, '0');
  for (unsigned I = 0; I < 32; ++I)
    if ((U >> I) & 1)
      B[31 - I] = '1';
  return B;
}

inline void fp_conformance_semantics(const camada::SMTSolverRef &solver,
                                     camada::FPEncoding Enc) {
  const std::vector<float> Vals = conformanceValues();
  auto C = [&](float F) { return solver->mkFPFromBin(floatBits(F), 8, Enc); };
  auto B = [&](bool V) { return solver->mkBool(V); };

  // Comparisons over every ordered pair. The host's own comparisons are
  // the reference: C++ implements IEEE semantics, so NaN and signed-zero
  // behaviour comes out of the language rather than being restated here
  // (and restating it is how a reference model acquires the same bug it
  // is meant to catch).
  {
    solver->reset();
    camada::SMTExprRef All = solver->mkBool(true);
    for (float A : Vals) {
      for (float D : Vals) {
        auto eq = [&](const camada::SMTExprRef &E, bool Want) {
          All = solver->mkAnd(All, solver->mkEqual(E, B(Want)));
        };
        eq(solver->mkFPLt(C(A), C(D)), A < D);
        eq(solver->mkFPLe(C(A), C(D)), A <= D);
        eq(solver->mkFPGt(C(A), C(D)), A > D);
        eq(solver->mkFPGe(C(A), C(D)), A >= D);
        eq(solver->mkFPEqual(C(A), C(D)), A == D);
      }
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // The properties that make those semantics distinctive, asserted
  // directly so a failure names the rule rather than a value pair.
  {
    solver->reset();
    camada::SMTExprRef NaN = C(std::numeric_limits<float>::quiet_NaN());
    camada::SMTExprRef PZero = C(0.0f), NZero = C(-0.0f);
    camada::SMTExprRef All = solver->mkAnd(
        // NaN is unordered with itself: every comparison is false.
        solver->mkAnd(solver->mkNot(solver->mkFPEqual(NaN, NaN)),
                      solver->mkNot(solver->mkFPLt(NaN, NaN))),
        solver->mkAnd(solver->mkNot(solver->mkFPGt(NaN, NaN)),
                      solver->mkNot(solver->mkFPLe(NaN, NaN))));
    // The zeros are distinct bit patterns but compare equal.
    All = solver->mkAnd(All, solver->mkFPEqual(PZero, NZero));
    All = solver->mkAnd(All, solver->mkFPLe(PZero, NZero));
    All = solver->mkAnd(All, solver->mkNot(solver->mkFPLt(PZero, NZero)));
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Absolute value clears the sign, including on infinities; on NaN the
  // result stays NaN. Comparing values rather than bits keeps this true
  // under both encodings, since a NaN's payload is not preserved.
  {
    solver->reset();
    camada::SMTExprRef All = solver->mkBool(true);
    for (float A : Vals) {
      camada::SMTExprRef Abs = solver->mkFPAbs(C(A));
      if (std::isnan(A))
        All = solver->mkAnd(All, solver->mkFPIsNaN(Abs));
      else
        All = solver->mkAnd(All, solver->mkFPEqual(Abs, C(std::fabs(A))));
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // The NaN and infinity constructors agree with the same values built
  // from their bit patterns.
  {
    solver->reset();
    const float Inf = std::numeric_limits<float>::infinity();
    camada::SMTExprRef All =
        solver->mkAnd(solver->mkFPEqual(solver->mkInf32(false, Enc), C(Inf)),
                      solver->mkFPEqual(solver->mkInf32(true, Enc), C(-Inf)));
    All = solver->mkAnd(
        All, solver->mkFPIsInfinite(solver->mkInf(false, 8, 24, Enc)));
    All = solver->mkAnd(All, solver->mkFPIsNaN(solver->mkNaN32(false, Enc)));
    All = solver->mkAnd(All, solver->mkFPIsNaN(solver->mkNaN32(true, Enc)));
    All =
        solver->mkAnd(All, solver->mkFPIsNaN(solver->mkNaN(false, 8, 24, Enc)));
    All = solver->mkAnd(All, solver->mkFPIsNaN(solver->mkNaN64(false, Enc)));
    All =
        solver->mkAnd(All, solver->mkFPIsInfinite(solver->mkInf64(true, Enc)));
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Widening float to double is exact, so converting and comparing
  // against the same value as a double round-trips for every input.
  {
    solver->reset();
    camada::SMTSortRef F64 = solver->mkFP64Sort(Enc);
    camada::SMTExprRef RNE = solver->mkRM(camada::RM::ROUND_TO_EVEN, Enc);
    camada::SMTExprRef All = solver->mkBool(true);
    for (float A : Vals) {
      camada::SMTExprRef Wide = solver->mkFPtoFP(C(A), F64, RNE);
      if (std::isnan(A)) {
        All = solver->mkAnd(All, solver->mkFPIsNaN(Wide));
        continue;
      }
      camada::SMTExprRef Want = solver->mkFP64((double)A, Enc);
      All = solver->mkAnd(All, solver->mkFPEqual(Wide, Want));
    }
    solver->addConstraint(All);
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }
}

} // namespace camada_fp_conformance

using camada_fp_conformance::fp_conformance_semantics;

#endif // CAMADA_REGRESSION_FPCONFORMANCE_TEST_H_
