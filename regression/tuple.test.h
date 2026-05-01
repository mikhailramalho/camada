
#include <catch2/catch_test_macros.hpp>

// Bool + BV only — works on every backend, including those without Int
// support (bitwuzla, stp, yices). Backends that lack native datatype
// support exercise the Camada-managed encoding here.
inline void tuple_semantics(const camada::SMTSolverRef &solver) {
  auto boolSort = solver->mkBoolSort();
  auto bv8Sort = solver->mkBVSort(8);
  auto tupleSort = solver->mkTupleSort({boolSort, bv8Sort});

  REQUIRE(tupleSort->isTupleSort());
  REQUIRE(tupleSort->getTupleElementSorts().size() == 2);
  REQUIRE(tupleSort->getTupleElementSorts()[0] == boolSort);
  REQUIRE(tupleSort->getTupleElementSorts()[1] == bv8Sort);

  auto tupleValue =
      solver->mkTuple({solver->mkBool(true), solver->mkBVFromDec(42, 8)});

  auto tupleSymbol = solver->mkSymbol("t", tupleSort);
  solver->addConstraint(solver->mkEqual(tupleSymbol, tupleValue));

  auto b = solver->mkTupleSelect(tupleSymbol, 0);
  auto bv = solver->mkTupleSelect(tupleSymbol, 1);

  REQUIRE(b->Sort == boolSort);
  REQUIRE(bv->Sort == bv8Sort);

  solver->addConstraint(solver->mkEqual(b, solver->mkBool(true)));
  solver->addConstraint(solver->mkEqual(bv, solver->mkBVFromDec(42, 8)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto b_res = solver->getBool(b);
  auto bv_res = solver->getBV(bv);
  REQUIRE(b_res);
  REQUIRE(bv_res);
  REQUIRE(b_res.value());
  REQUIRE(bv_res.value() == 42);
}

// Bool + BV + Int — only run against backends with Int support
// (z3, cvc5). Kept separate so the Int-free fixture above can run on
// every backend via the shared tests(solver) runner.
inline void tuple_semantics_with_int(const camada::SMTSolverRef &solver) {
  auto boolSort = solver->mkBoolSort();
  auto bv8Sort = solver->mkBVSort(8);
  auto intSort = solver->mkIntSort();
  auto tupleSort = solver->mkTupleSort({boolSort, bv8Sort, intSort});

  auto tupleValue = solver->mkTuple(
      {solver->mkBool(true), solver->mkBVFromDec(42, 8), solver->mkInt(7)});

  auto tupleSymbol = solver->mkSymbol("t_int", tupleSort);
  solver->addConstraint(solver->mkEqual(tupleSymbol, tupleValue));

  auto i = solver->mkTupleSelect(tupleSymbol, 2);
  REQUIRE(i->Sort == intSort);
  solver->addConstraint(solver->mkEqual(i, solver->mkInt(7)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

// Tuple whose second field is an array. Exercises the encoded path's
// per-field decomposition for non-scalar field sorts: on backends
// without native datatype support, the array field becomes a regular
// array-typed symbol named __CAMADA_tup_<base>_1 minted on demand.
//
// Skipped on yices-smt2 SMT-LIB pipeline (which rejects mkArrayConst —
// this fixture intentionally avoids it). Works on every native backend
// and on the SMT-LIB pipeline against z3/cvc5/bitwuzla/mathsat.
inline void tuple_with_array_field(const camada::SMTSolverRef &solver) {
  auto bv8 = solver->mkBVSort(8);
  auto idxSort = solver->mkBVSort(3);
  auto arrSort = solver->mkArraySort(idxSort, bv8);
  auto tupleSort = solver->mkTupleSort({bv8, arrSort});

  REQUIRE(tupleSort->isTupleSort());
  REQUIRE(tupleSort->getTupleElementSorts().size() == 2);
  REQUIRE(tupleSort->getTupleElementSorts()[1] == arrSort);

  auto t = solver->mkSymbol("t_arr", tupleSort);
  auto bvField = solver->mkTupleSelect(t, 0);
  auto arrField = solver->mkTupleSelect(t, 1);
  REQUIRE(bvField->Sort == bv8);
  REQUIRE(arrField->Sort == arrSort);

  // Constrain the BV field to 7 and require arrField[3] == 42.
  solver->addConstraint(solver->mkEqual(bvField, solver->mkBVFromDec(7, 8)));
  auto idx = solver->mkBVFromDec(3, idxSort);
  auto fortyTwo = solver->mkBVFromDec(42, 8);
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(arrField, idx), fortyTwo));

  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto bv_res = solver->getBV(bvField);
  REQUIRE(bv_res);
  REQUIRE(bv_res.value() == 7);
  auto sel_res = solver->getBV(solver->mkArraySelect(arrField, idx));
  REQUIRE(sel_res);
  REQUIRE(sel_res.value() == 42);
}

// Pin host-side AST equality for tuple expressions: two freshly built
// CamadaTupleExpr nodes that describe the same shape with structurally
// equal components compare equal via SMTExpr::operator==. Distinct
// components (different bool, different bv, different symbol name)
// compare unequal. Native-tuple backends already get this for free via
// their backend term; the encoded path needs to implement it on
// CamadaTupleExpr explicitly.
inline void tuple_structural_equality(const camada::SMTSolverRef &solver) {
  auto boolSort = solver->mkBoolSort();
  auto bv8Sort = solver->mkBVSort(8);
  auto tupleSort = solver->mkTupleSort({boolSort, bv8Sort});

  auto t1 = solver->mkTuple({solver->mkBool(true), solver->mkBVFromDec(42, 8)});
  auto t1_alias =
      solver->mkTuple({solver->mkBool(true), solver->mkBVFromDec(42, 8)});
  auto t2 =
      solver->mkTuple({solver->mkBool(false), solver->mkBVFromDec(42, 8)});

  REQUIRE(*t1 == *t1);
  REQUIRE(*t1 == *t1_alias);
  REQUIRE_FALSE(*t1 == *t2);

  // Symbols: same (name, sort) → equal; different name → not.
  auto sym_a = solver->mkSymbol("tup_a", tupleSort);
  auto sym_b = solver->mkSymbol("tup_b", tupleSort);
  // mkSymbol caches by (name, sort), so the same name returns the same
  // handle. Use the underlying expr equality to verify the path works
  // even when handle identity coincides with structural identity.
  REQUIRE(*sym_a == *sym_a);
  REQUIRE_FALSE(*sym_a == *sym_b);
}

inline void empty_tuple_semantics(const camada::SMTSolverRef &solver) {
  auto tupleSort = solver->mkTupleSort({});
  auto tupleValue = solver->mkTuple({});

  REQUIRE(tupleSort->isTupleSort());
  REQUIRE(tupleSort->getTupleElementSorts().empty());
  REQUIRE(tupleValue->Sort == tupleSort);

  auto tupleSymbol = solver->mkSymbol("empty_tuple", tupleSort);
  REQUIRE(tupleSymbol->Sort == tupleSort);

  solver->addConstraint(solver->mkEqual(tupleSymbol, tupleValue));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}
