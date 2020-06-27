
#include "camada.h"

#include <catch2/catch.hpp>

inline void equal_ten(const camada::SMTSolverRef &solver) {
  // A free variable
  auto f = solver->mkSymbol("f", solver->getBitvectorSort(10));

  // And assert if there is a value for 'f' that is equal to 10
  auto ten = solver->mkBitvector(10, 10);
  auto eq = solver->mkEqual(f, ten);

  // Add the constraint to the solver
  solver->addConstraint(eq);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::checkResult::SAT);

  int64_t f_res = solver->getBitvector(f);
  REQUIRE(f_res == 10);
  REQUIRE(f_res == solver->getBitvector(ten));
}