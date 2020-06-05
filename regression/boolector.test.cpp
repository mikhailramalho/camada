

#include "camada.h"
#include "simple.test.h"

#include <boolectorsolver.h>
#include <catch2/catch.hpp>

TEST_CASE("Simple Boolector test", "[Boolector]") {
  // Create Boolector Solver
  auto btor = camada::createBoolectorSolver();
  equal_ten(btor);
}
