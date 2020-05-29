#define CATCH_CONFIG_MAIN
#include <catch2/catch.hpp>

#include <camada.h>

#ifdef SOLVER_Z3_ENABLED

#include <z3++.h>
#include <z3solver.h>

void equal_ten(camada::SMTSolverRef solver) {
  // A free variable
  auto f = solver->mkSymbol("f", solver->getBitvectorSort(10));

  // And assert if there is a value for 'f' that is equal to 10
  auto ten = solver->mkBitvector(std::to_string(10), 10);
  auto eq = solver->mkEqual(f, ten);

  // Add the constraint to the solver
  solver->addConstraint(eq);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::checkResult::SAT);

  std::string f_res;
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
    myZ3Solver(camada::Z3ContextRef C) : camada::Z3Solver() {
      Context = C;

      camada::Z3Tactic t1(Context, Z3_mk_tactic(Context->Context, "simplify"));
      camada::Z3Tactic t2(Context, Z3_mk_tactic(Context->Context, "solve-eqs"));
      camada::Z3Tactic t3(Context, Z3_mk_tactic(Context->Context, "simplify"));
      camada::Z3Tactic t4(Context, Z3_mk_tactic(Context->Context, "smt"));

      camada::Z3Tactic t(
          Context,
          Z3_tactic_and_then(
              Context->Context, t1.Tactic,
              Z3_tactic_and_then(
                  Context->Context, t2.Tactic,
                  Z3_tactic_and_then(Context->Context, t3.Tactic, t4.Tactic))));

      Solver = Z3_mk_solver_from_tactic(Context->Context, t.Tactic);
      Z3_solver_inc_ref(Context->Context, Solver);
    }
  };

  // Create Z3 Solver
  camada::SMTSolverRef z3 = std::make_shared<camada::Z3Solver>(
      std::make_shared<camada::Z3Context>(std::move(camada::Z3Config())));

  equal_ten(z3);
}

#endif
