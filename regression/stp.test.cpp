#include "tests.h"
#include "matrix.test.h"

// One test case per shared fixture group; capability gates and
// exclusions live in matrix.test.h.
CAMADA_SHARED_MATRIX(STP, camada::createSTPSolver)

#include <catch2/catch_test_macros.hpp>
#include <solvers/stpsolver.h>

TEST_CASE("STP feature capabilities", "[STP]") {
  auto solver = camada::createSTPSolver();
  using camada::SolverFeature;
  REQUIRE(solver->getSolverKind() == camada::SolverKind::STP);
  REQUIRE_FALSE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE_FALSE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE_FALSE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE_FALSE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(solver->supports(SolverFeature::Timeouts));
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

TEST_CASE("Unsupported nested constant arrays STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() { nested_const_array_semantics(stp); });
}
