

#include "camada.h"
#include "simple.test.h"

#include <catch2/catch.hpp>
#include <z3++.h>
#include <z3solver.h>

TEST_CASE("Simple Z3 test", "[Z3]") {
  // Create Z3 Solver
  auto z3 = camada::createZ3Solver();
  equal_ten(z3);
}

TEST_CASE("Override Z3 Solver", "[Z3]") {

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
      std::make_shared<myZ3Solver>(std::make_shared<z3::context>());

  equal_ten(z3);
}
