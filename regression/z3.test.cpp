
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <z3solver.h>

TEST_CASE("Simple Z3 test", "[Z3]") {
  // Create Z3 Solver
  auto z3 = camada::createZ3Solver();
  tests(z3);
}

TEST_CASE("Quantifiers Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  quantifier_semantics(z3);
}

TEST_CASE("UF Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  uf_semantics(z3);
}

TEST_CASE("Arith Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  int_arithmetic_semantics(z3);
  z3->reset();
  real_arithmetic_semantics(z3);
}

TEST_CASE("Override Z3 Solver", "[Z3]") {

  class myZ3Solver : public camada::Z3Solver {
  public:
    explicit myZ3Solver(std::unique_ptr<z3::context> C)
        : camada::Z3Solver(std::move(C)) {
      Solver = makeSolver(*Context);
    }

  private:
    static z3::solver makeSolver(z3::context &C) {
      return (z3::tactic(C, "simplify") & z3::tactic(C, "solve-eqs") &
              z3::tactic(C, "simplify") & z3::tactic(C, "smt"))
          .mk_solver();
    }
  };

  // Create Z3 Solver
  camada::SMTSolverRef z3 =
      std::make_unique<myZ3Solver>(std::make_unique<z3::context>());

  tests(z3);
}
