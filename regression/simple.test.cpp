#define CATCH_CONFIG_MAIN
#include <catch2/catch.hpp>

#include <camada.h>

TEST_CASE("Simple test", "[Basic]") {
  // Create Z3 Solver
  auto z3 = camada::createZ3Solver();

  // A free variable
  auto f = z3->mkSymbol("f", z3->getBitvectorSort(10));

  // And assert if there is a value for 'f' that is equal to 10
  auto ten = z3->mkBitvector(std::to_string(10), 10);
  auto eq = z3->mkEqual(f, ten);

  // Add the constraint to the solver
  z3->addConstraint(eq);

  // And check for satisfiability
  REQUIRE(z3->check() == camada::checkResult::SAT);

  std::string f_res;
  REQUIRE(z3->getInterpretation(f, f_res));
  REQUIRE(f_res == z3->getBitvector(ten));
}
