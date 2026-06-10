
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
