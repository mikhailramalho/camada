
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

TEST_CASE("Arith CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  int_arithmetic_semantics(cvc5);
  cvc5->reset();
  real_arithmetic_semantics(cvc5);
  cvc5->reset();
  arith_model_queries(cvc5);
  cvc5->reset();
  arith_conversion_semantics(cvc5);
  cvc5->reset();
  arith_symbolic_shift_semantics(cvc5);
}

TEST_CASE("Tuple CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  tuple_semantics(cvc5);
}
