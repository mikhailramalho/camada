
#include "tests.h"

#include <catch2/catch.hpp>
#include <stpsolver.h>

TEST_CASE("Simple STP test", "[STP]") {
  // Create STP Solver
  auto stp = camada::createSTPSolver();
  tests(stp);
  delete stp;
}
