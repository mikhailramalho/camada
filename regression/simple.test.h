
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

inline void implies_semantics(const camada::SMTSolverRef &solver) {
  auto f1 = solver->mkBool(false);
  auto implication = solver->mkImplies(f1, f1);
  REQUIRE(f1->getKind() == camada::SMTExprKind::BoolConst);
  REQUIRE(implication->getKind() == camada::SMTExprKind::Implies);
  solver->addConstraint(solver->mkNot(implication));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

inline void implies_true_implies_false(const camada::SMTSolverRef &solver) {
  auto t = solver->mkBool(true);
  auto f = solver->mkBool(false);
  REQUIRE(t->getKind() == camada::SMTExprKind::BoolConst);
  REQUIRE(f->getKind() == camada::SMTExprKind::BoolConst);
  auto implication = solver->mkImplies(t, f);
  REQUIRE(implication->getKind() == camada::SMTExprKind::Implies);
  solver->addConstraint(implication);
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

inline void bv_lshr_semantics(const camada::SMTSolverRef &solver) {
  auto value = solver->mkBVFromBin("1000", 4);
  auto shift = solver->mkBVFromDec(1, 4);
  auto result = solver->mkBVLshr(value, shift);
  REQUIRE(value->getKind() == camada::SMTExprKind::BVConst);
  REQUIRE(shift->getKind() == camada::SMTExprKind::BVConst);
  REQUIRE(result->getKind() == camada::SMTExprKind::BVLshr);

  solver->addConstraint(
      solver->mkEqual(result, solver->mkBVFromBin("0100", 4)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

inline void incremental_push_pop(const camada::SMTSolverRef &solver) {
  auto x = solver->mkSymbol("x", solver->mkBVSort(8));
  auto one = solver->mkBVFromDec(1, 8);
  auto two = solver->mkBVFromDec(2, 8);

  solver->addConstraint(solver->mkEqual(x, one));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  solver->push();
  solver->addConstraint(solver->mkEqual(x, two));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  solver->pop();
  REQUIRE(solver->check() == camada::checkResult::SAT);
  REQUIRE(solver->getBV(x) == 1);
}
