
#include "tests.h"

#include <catch2/catch.hpp>
#include <cvc5solver.h>

TEST_CASE("Simple CVC5 test", "[CVC5]") {
  // Create CVC5 Solver
  auto cvc5 = camada::createCVC5Solver();
  tests(cvc5);
}
