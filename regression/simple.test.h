
#include "camada.h"

#include <bitset>
#include <catch2/catch_test_macros.hpp>
#include <string>

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

inline void fp_equal(const camada::SMTSolverRef &solver,
                     camada::FPEncoding Encoding) {
  auto x = solver->mkFP32(0.06f, Encoding);
  auto y = solver->mkFP64(-7.0, Encoding);
  REQUIRE(x->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(y->getKind() == camada::SMTExprKind::FPConst);

  auto fx = solver->mkSymbol("fx", solver->mkFP32Sort(Encoding));
  auto fy = solver->mkSymbol("fy", solver->mkFP64Sort(Encoding));
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

inline void
handle_invalidation_after_reset(const camada::SMTSolverRef &solver) {
  auto sort = solver->mkBVSort(8);
  auto expr = solver->mkSymbol("stale", sort);

  REQUIRE(sort.isValid());
  REQUIRE(expr.isValid());

  solver->reset();

  REQUIRE_FALSE(sort.isValid());
  REQUIRE_FALSE(expr.isValid());

  auto fresh_sort = solver->mkBVSort(8);
  auto fresh_expr = solver->mkSymbol("fresh", fresh_sort);
  REQUIRE(fresh_sort.isValid());
  REQUIRE(fresh_expr.isValid());
}

inline void quantifier_semantics(const camada::SMTSolverRef &solver) {
  auto x = solver->mkSymbol("x", solver->mkBVSort(4));
  solver->addConstraint(solver->mkForall({x}, solver->mkEqual(x, x)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  solver->reset();
  x = solver->mkSymbol("x", solver->mkBVSort(4));
  auto three = solver->mkBVFromDec(3, 4);
  solver->addConstraint(solver->mkExists({x}, solver->mkEqual(x, three)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  solver->reset();
  x = solver->mkSymbol("x", solver->mkBVSort(4));
  three = solver->mkBVFromDec(3, 4);
  solver->addConstraint(solver->mkForall({x}, solver->mkEqual(x, three)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

inline void uf_semantics(const camada::SMTSolverRef &solver) {
  auto bv4 = solver->mkBVSort(4);
  auto fsort = solver->mkFunctionSort({bv4}, bv4);
  auto f = solver->mkSymbol("f", fsort);
  auto x = solver->mkSymbol("x", bv4);
  auto y = solver->mkSymbol("y", bv4);
  auto fx = solver->mkApply(f, {x});
  auto fy = solver->mkApply(f, {y});
  REQUIRE(f->getKind() == camada::SMTExprKind::Symbol);
  REQUIRE(fx->getKind() == camada::SMTExprKind::Apply);
  REQUIRE(fy->getKind() == camada::SMTExprKind::Apply);

  solver->addConstraint(solver->mkEqual(x, y));
  solver->addConstraint(solver->mkNot(solver->mkEqual(fx, fy)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

inline void dump_string_semantics(const camada::SMTSolverRef &solver) {
  auto bv8 = solver->mkBVSort(8);
  auto x = solver->mkSymbol("x", bv8);
  auto five = solver->mkBVFromDec(5, 8);
  solver->addConstraint(solver->mkEqual(x, five));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  std::string sort_dump = "seed";
  bv8->dump(sort_dump);
  REQUIRE(!sort_dump.empty());
  REQUIRE(sort_dump != "seed");

  std::string expr_dump = "seed";
  x->dump(expr_dump);
  REQUIRE(!expr_dump.empty());
  REQUIRE(expr_dump != "seed");

  std::string solver_dump = "seed";
  solver->dump(solver_dump);
  REQUIRE(!solver_dump.empty());
  REQUIRE(solver_dump != "seed");

  std::string model_dump = "seed";
  solver->dumpModel(model_dump);
  REQUIRE(!model_dump.empty());
  REQUIRE(model_dump != "seed");
}

inline void int_arithmetic_semantics(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto x = solver->mkSymbol("x", int_sort);
  auto one = solver->mkInt(1);
  auto two = solver->mkInt(2);
  auto three = solver->mkInt(3);

  auto x_plus_one = solver->mkArithAdd(x, one);
  REQUIRE(x_plus_one->getKind() == camada::SMTExprKind::ArithAdd);

  solver->addConstraint(solver->mkEqual(x_plus_one, three));
  solver->addConstraint(solver->mkArithGt(x, two));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  solver->reset();
  int_sort = solver->mkIntSort();
  x = solver->mkSymbol("x", int_sort);
  one = solver->mkInt(1);
  two = solver->mkInt(2);
  three = solver->mkInt(3);
  x_plus_one = solver->mkArithAdd(x, one);
  solver->addConstraint(solver->mkEqual(x_plus_one, three));
  solver->addConstraint(solver->mkArithGt(x, one));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

inline void real_arithmetic_semantics(const camada::SMTSolverRef &solver) {
  auto real_sort = solver->mkRealSort();
  auto r = solver->mkSymbol("r", real_sort);
  auto one = solver->mkReal(1);
  auto two = solver->mkReal(2);
  auto three = solver->mkReal(3);

  auto r_plus_one = solver->mkArithAdd(r, one);
  REQUIRE(r_plus_one->getKind() == camada::SMTExprKind::ArithAdd);

  solver->addConstraint(solver->mkEqual(r_plus_one, three));
  solver->addConstraint(solver->mkArithGt(r, one));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  solver->reset();
  real_sort = solver->mkRealSort();
  r = solver->mkSymbol("r", real_sort);
  one = solver->mkReal(1);
  two = solver->mkReal(2);
  three = solver->mkReal(3);
  (void)two;
  (void)three;
  solver->addConstraint(solver->mkEqual(r, one));
  solver->addConstraint(solver->mkArithLt(r, one));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

inline void arith_model_queries(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto real_sort = solver->mkRealSort();

  auto x = solver->mkSymbol("x", int_sort);
  auto r = solver->mkSymbol("r", real_sort);
  auto x_plus_two = solver->mkArithAdd(x, solver->mkInt("2"));
  auto r_plus_half = solver->mkArithAdd(r, solver->mkReal(1, 2));

  solver->addConstraint(solver->mkEqual(x, solver->mkInt(5)));
  solver->addConstraint(solver->mkEqual(r, solver->mkReal(3, 2)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  REQUIRE(solver->getInt(x) == "5");
  REQUIRE(solver->getInt(x_plus_two) == "7");

  std::string num;
  std::string den;
  solver->getRational(r, num, den);
  REQUIRE(num == "3");
  REQUIRE(den == "2");
  REQUIRE(solver->getRealNumerator(r) == "3");
  REQUIRE(solver->getRealDenominator(r) == "2");

  REQUIRE(solver->getInt(r_plus_half) == "2");
}

inline void arith_conversion_semantics(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto real_sort = solver->mkRealSort();

  auto x = solver->mkSymbol("x", int_sort);
  auto r = solver->mkSymbol("r", real_sort);

  auto x_real = solver->mkInt2Real(x);
  auto r_int = solver->mkReal2Int(r);
  auto r_is_int = solver->mkIsInt(r);
  auto x_real_is_int = solver->mkIsInt(x_real);
  auto mod_expr = solver->mkArithMod(solver->mkInt("17"), solver->mkInt("5"));
  auto shl_expr = solver->mkArithShl(x, 3);

  REQUIRE(x_real->getKind() == camada::SMTExprKind::Int2Real);
  REQUIRE(r_int->getKind() == camada::SMTExprKind::Real2Int);
  REQUIRE(r_is_int->getKind() == camada::SMTExprKind::IsInt);
  REQUIRE(mod_expr->getKind() == camada::SMTExprKind::ArithMod);
  REQUIRE(shl_expr->getKind() == camada::SMTExprKind::ArithShl);

  solver->addConstraint(solver->mkEqual(x, solver->mkInt("5")));
  solver->addConstraint(solver->mkEqual(r, solver->mkReal(7, 2)));
  solver->addConstraint(solver->mkEqual(x_real, solver->mkReal("5")));
  solver->addConstraint(solver->mkEqual(r_int, solver->mkInt("3")));
  solver->addConstraint(solver->mkNot(r_is_int));
  solver->addConstraint(x_real_is_int);
  solver->addConstraint(solver->mkEqual(mod_expr, solver->mkInt("2")));
  solver->addConstraint(solver->mkEqual(shl_expr, solver->mkInt("40")));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

inline void arith_symbolic_shift_semantics(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto x = solver->mkSymbol("x", int_sort);
  auto k = solver->mkSymbol("k", int_sort);
  auto shl_expr = solver->mkArithShl(x, k);

  REQUIRE(shl_expr->getKind() == camada::SMTExprKind::ArithShl);

  solver->addConstraint(solver->mkEqual(x, solver->mkInt("5")));
  solver->addConstraint(solver->mkEqual(k, solver->mkInt("3")));
  solver->addConstraint(solver->mkEqual(shl_expr, solver->mkInt("40")));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}
