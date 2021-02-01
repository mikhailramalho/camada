
#include "camada.h"

#include <catch2/catch.hpp>

inline void fp_arithmetics(const camada::SMTSolverRef &solver) {
  auto x = solver->mkFP32(0.750000059604644775390625f);
  auto y = solver->mkFP32(0.750000059604644775390625f);

  auto zero = solver->mkFP32(0.f);
  auto one = solver->mkFP32(1.f);
  auto two = solver->mkFP32(2.f);

  // Add
  solver->addConstraint(solver->mkEqual(
      solver->mkFPAdd(x, solver->mkFPNeg(y), camada::RM::ROUND_TO_EVEN), zero));

  // sub
  solver->addConstraint(
      solver->mkEqual(solver->mkFPSub(x, y, camada::RM::ROUND_TO_EVEN), zero));

  // mul
  auto mul = solver->mkFP32(0.562500119209f);
  solver->addConstraint(
      solver->mkEqual(solver->mkFPMul(x, y, camada::RM::ROUND_TO_EVEN), mul));

  // div
  solver->addConstraint(
      solver->mkEqual(solver->mkFPDiv(x, y, camada::RM::ROUND_TO_EVEN), one));

  // sqrt
  solver->addConstraint(
      solver->mkEqual(solver->mkFPSqrt(one, camada::RM::ROUND_TO_EVEN), one));

  // rem
  solver->addConstraint(solver->mkEqual(solver->mkFPRem(x, y), zero));

  // fma
  solver->addConstraint(solver->mkEqual(
      solver->mkFPFMA(one, two, zero, camada::RM::ROUND_TO_EVEN), two));

  // And check for satisfiability
  REQUIRE(solver->check() == camada::checkResult::SAT);
}