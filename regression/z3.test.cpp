#define CATCH_CONFIG_MAIN
#include <catch2/catch.hpp>

#include <camada.h>

#ifdef SOLVER_Z3_ENABLED

#include <z3++.h>
#include <z3solver.h>

void equal_ten(const camada::SMTSolverRef &solver) {
  // A free variable
  auto f = solver->mkSymbol("f", solver->getBitvectorSort(10));

  // And assert if there is a value for 'f' that is equal to 10
  auto ten = solver->mkBitvector(10, 10);
  auto eq = solver->mkEqual(f, ten);

  // Add the constraint to the solver
  solver->addConstraint(eq);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::checkResult::SAT);

  int64_t f_res;
  REQUIRE(solver->getInterpretation(f, f_res));
  REQUIRE(f_res == solver->getBitvector(ten));
}

TEST_CASE("Simple test", "[Z3]") {
  // Create Z3 Solver
  auto z3 = camada::createZ3Solver();
  equal_ten(z3);
}

TEST_CASE("Override Solver", "[Z3]") {

  class myZ3Solver : public camada::Z3Solver {
  public:
    explicit myZ3Solver(const camada::Z3ContextRef &C)
        : camada::Z3Solver(
              C, (z3::tactic(*C, "simplify") & z3::tactic(*C, "solve-eqs") &
                  z3::tactic(*C, "simplify") & z3::tactic(*C, "smt"))
                     .mk_solver()) {}
  };

  // Create Z3 Solver
  camada::SMTSolverRef z3 =
      std::make_shared<camada::Z3Solver>(std::make_shared<z3::context>());

  equal_ten(z3);
}

#endif
