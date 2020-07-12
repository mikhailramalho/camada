
#include "tests.h"

#include <catch2/catch.hpp>
#include <cvc4solver.h>

TEST_CASE("Simple CVC4 test", "[CVC4]") {
  // Create CVC4 Solver
  auto cvc4 = camada::createCVC4Solver();
  tests(cvc4);
}
