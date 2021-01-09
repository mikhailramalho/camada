
#include "camada.h"

#include <bitset>
#include <catch2/catch.hpp>

inline void equal_ten(const camada::SMTSolverRef &solver) {
  // A free variable
  auto f = solver->mkSymbol("f", solver->mkBVSort(10));

  // And assert if there is a value for 'f' that is equal to 10
  auto ten = solver->mkBVFromBin(std::bitset<10>(-10).to_string(), 10);
  auto eq = solver->mkEqual(f, ten);

  // Add the constraint to the solver
  solver->addConstraint(eq);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::checkResult::SAT);

  int64_t f_res = solver->getBV(f);
  REQUIRE(f_res == -10);
  REQUIRE(f_res == solver->getBV(ten));
}

inline void fp_equal(const camada::SMTSolverRef &solver) {
  auto x = solver->mkFP32(0.06f);
  auto y = solver->mkFP64(-7.0);

  auto fx = solver->mkSymbol("fx", solver->mkFP32Sort());
  auto fy = solver->mkSymbol("fy", solver->mkFP64Sort());

  // Add the constraint to the solver
  solver->addConstraint(solver->mkEqual(fy, y));
  solver->addConstraint(solver->mkEqual(fx, x));

  // And check for satisfiability
  REQUIRE(solver->check() == camada::checkResult::SAT);
  REQUIRE(solver->getFP32(fx) == 0.06f);
  REQUIRE(solver->getFP64(fy) == -7.0);
}