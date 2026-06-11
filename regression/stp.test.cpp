
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <stpsolver.h>

TEST_CASE("Simple STP test", "[STP]") {
  // Create STP Solver
  auto stp = camada::createSTPSolver();
  tests(stp);
}

TEST_CASE("Unsupported UF STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    auto fn = stp->mkFunctionSort({bv4}, bv4);
    (void)stp->mkSymbol("f", fn);
  });
}

TEST_CASE("STP feature capabilities", "[STP]") {
  auto solver = camada::createSTPSolver();
  using camada::SolverFeature;
  REQUIRE_FALSE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE_FALSE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE_FALSE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE_FALSE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE_FALSE(solver->supports(SolverFeature::Timeouts));
  REQUIRE_FALSE(solver->supports(SolverFeature::ArrayModels));
}

TEST_CASE("Unsupported nested arrays STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    (void)stp->mkArraySort(bv4, stp->mkArraySort(bv4, bv4));
  });
}

TEST_CASE("Unsupported tuple-array UF/quantifier boundaries STP test",
          "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    auto tupArr = stp->mkArraySort(bv4, stp->mkTupleSort({bv4}));
    (void)stp->mkFunctionSort({tupArr}, bv4);
  });
}

TEST_CASE("Unsupported nested constant tuple arrays STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    auto init = stp->mkTuple({stp->mkBool(true), stp->mkBVFromDec(5, 8)});
    auto innerConst = stp->mkArrayConst(bv4, init);
    (void)stp->mkArrayConst(bv4, innerConst);
  });
}
