
#include "camada.h"

#include <bitset>
#include <catch2/catch_test_macros.hpp>

inline void equal_ten(const camada::SMTSolverRef &solver) {
  // A free variable
  auto f = solver->mkSymbol("f", solver->mkBVSort(10));
  REQUIRE(f->getKind() == camada::SMTExprKind::Symbol);

  // And assert if there is a value for 'f' that is equal to 10
  auto ten = solver->mkBVFromBin(std::bitset<10>(-10).to_string(), 10);
  REQUIRE(ten->getKind() == camada::SMTExprKind::BVConst);
  auto eq = solver->mkEqual(f, ten);
  REQUIRE(eq->getKind() == camada::SMTExprKind::Equal);

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
  REQUIRE(x->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(y->getKind() == camada::SMTExprKind::FPConst);

  auto fx = solver->mkSymbol("fx", solver->mkFP32Sort());
  auto fy = solver->mkSymbol("fy", solver->mkFP64Sort());
  REQUIRE(fx->getKind() == camada::SMTExprKind::Symbol);
  REQUIRE(fy->getKind() == camada::SMTExprKind::Symbol);

  // Add the constraint to the solver
  auto eqy = solver->mkEqual(fy, y);
  auto eqx = solver->mkEqual(fx, x);
  REQUIRE(eqy->getKind() == camada::SMTExprKind::Equal);
  REQUIRE(eqx->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(eqy);
  solver->addConstraint(eqx);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::checkResult::SAT);
  REQUIRE(solver->getFP32(fx) == 0.06f);
  REQUIRE(solver->getFP64(fy) == -7.0);
}
