
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <cvc5solver.h>

TEST_CASE("Simple CVC5 test", "[CVC5]") {
  // Create CVC5 Solver
  auto cvc5 = camada::createCVC5Solver();
  tests(cvc5);
}

TEST_CASE("Quantifiers CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  quantifier_semantics(cvc5);
}

TEST_CASE("UF CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  uf_semantics(cvc5);
}
