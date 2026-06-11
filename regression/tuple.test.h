
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
// mkTupleUpdate is ESBMC's `with`-on-struct choke point: a tuple equal
// to the original except at one field. Bool + BV only, like
// tuple_semantics, so every backend (native datatypes and the Camada
// per-field lowering) runs it.
inline void tuple_update_semantics(const camada::SMTSolverRef &solver) {
  auto boolSort = solver->mkBoolSort();
  auto bv8Sort = solver->mkBVSort(8);
  auto tupleSort = solver->mkTupleSort({boolSort, bv8Sort, bv8Sort});

  // Value tuple: the updated field changes, the others are preserved.
  auto t = solver->mkTuple({solver->mkBool(true), solver->mkBVFromDec(1, 8),
                            solver->mkBVFromDec(2, 8)});
  auto u = solver->mkTupleUpdate(t, 1, solver->mkBVFromDec(9, 8));
  REQUIRE(u->Sort == t->Sort);
  auto expected =
      solver->mkTuple({solver->mkBool(true), solver->mkBVFromDec(9, 8),
                       solver->mkBVFromDec(2, 8)});
  solver->addConstraint(solver->mkNot(solver->mkEqual(u, expected)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Symbol tuple: non-updated fields stay tied to the original symbol's
  // fields, and the updated field equals the new value.
  solver->reset();
  boolSort = solver->mkBoolSort();
  bv8Sort = solver->mkBVSort(8);
  tupleSort = solver->mkTupleSort({boolSort, bv8Sort, bv8Sort});
  auto s = solver->mkSymbol("st", tupleSort);
  auto v = solver->mkTupleUpdate(s, 2, solver->mkBVFromDec(7, 8));
  auto preserved = solver->mkAnd(
      solver->mkEqual(solver->mkTupleSelect(v, 0), solver->mkTupleSelect(s, 0)),
      solver->mkEqual(solver->mkTupleSelect(v, 1),
                      solver->mkTupleSelect(s, 1)));
  auto updated =
      solver->mkEqual(solver->mkTupleSelect(v, 2), solver->mkBVFromDec(7, 8));
  solver->addConstraint(solver->mkNot(solver->mkAnd(preserved, updated)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Chained updates of the same field — ESBMC's pointer-arithmetic hot
  // pattern — collapse to the last value with the other fields preserved.
  solver->reset();
  boolSort = solver->mkBoolSort();
  bv8Sort = solver->mkBVSort(8);
  tupleSort = solver->mkTupleSort({boolSort, bv8Sort, bv8Sort});
  auto base = solver->mkSymbol("base", tupleSort);
  auto twice = solver->mkTupleUpdate(
      solver->mkTupleUpdate(base, 1, solver->mkBVFromDec(1, 8)), 1,
      solver->mkBVFromDec(2, 8));
  auto chainOk = solver->mkAnd(solver->mkEqual(solver->mkTupleSelect(twice, 1),
                                               solver->mkBVFromDec(2, 8)),
                               solver->mkEqual(solver->mkTupleSelect(twice, 2),
                                               solver->mkTupleSelect(base, 2)));
  solver->addConstraint(solver->mkNot(chainOk));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Update of an ite-shaped tuple distributes through both branches.
  solver->reset();
  boolSort = solver->mkBoolSort();
  bv8Sort = solver->mkBVSort(8);
  tupleSort = solver->mkTupleSort({boolSort, bv8Sort, bv8Sort});
  auto ta = solver->mkSymbol("ta", tupleSort);
  auto tb = solver->mkSymbol("tb", tupleSort);
  auto cond = solver->mkSymbol("cond", solver->mkBoolSort());
  auto picked = solver->mkIte(cond, ta, tb);
  auto pickedUpd = solver->mkTupleUpdate(picked, 1, solver->mkBVFromDec(4, 8));
  auto iteOk = solver->mkAnd(
      solver->mkEqual(solver->mkTupleSelect(pickedUpd, 1),
                      solver->mkBVFromDec(4, 8)),
      solver->mkEqual(solver->mkTupleSelect(pickedUpd, 2),
                      solver->mkIte(cond, solver->mkTupleSelect(ta, 2),
                                    solver->mkTupleSelect(tb, 2))));
  solver->addConstraint(solver->mkNot(iteOk));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Updating the scalar field of a tuple that carries an array field
  // composes with the verbatim array storage in the Camada lowering.
  solver->reset();
  bv8Sort = solver->mkBVSort(8);
  auto arrSort = solver->mkArraySort(bv8Sort, bv8Sort);
  auto mixSort = solver->mkTupleSort({bv8Sort, arrSort});
  auto mix = solver->mkSymbol("mix", mixSort);
  auto mixUpd = solver->mkTupleUpdate(mix, 0, solver->mkBVFromDec(6, 8));
  auto arrPreserved =
      solver->mkEqual(solver->mkArraySelect(solver->mkTupleSelect(mixUpd, 1),
                                            solver->mkBVFromDec(0, 8)),
                      solver->mkArraySelect(solver->mkTupleSelect(mix, 1),
                                            solver->mkBVFromDec(0, 8)));
  auto scalarUpdated = solver->mkEqual(solver->mkTupleSelect(mixUpd, 0),
                                       solver->mkBVFromDec(6, 8));
  solver->addConstraint(
      solver->mkNot(solver->mkAnd(arrPreserved, scalarUpdated)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Nested tuples: updating an inner tuple through an outer update.
  solver->reset();
  boolSort = solver->mkBoolSort();
  bv8Sort = solver->mkBVSort(8);
  auto innerSort = solver->mkTupleSort({bv8Sort, bv8Sort});
  auto outerSort = solver->mkTupleSort({boolSort, innerSort});
  auto outer = solver->mkSymbol("outer", outerSort);
  auto newInner = solver->mkTupleUpdate(solver->mkTupleSelect(outer, 1), 0,
                                        solver->mkBVFromDec(3, 8));
  auto newOuter = solver->mkTupleUpdate(outer, 1, newInner);
  // inner[0] is 3, inner[1] is preserved, outer[0] is preserved
  auto innerOfNew = solver->mkTupleSelect(newOuter, 1);
  auto ok = solver->mkAnd(
      solver->mkAnd(solver->mkEqual(solver->mkTupleSelect(innerOfNew, 0),
                                    solver->mkBVFromDec(3, 8)),
                    solver->mkEqual(solver->mkTupleSelect(innerOfNew, 1),
                                    solver->mkTupleSelect(
                                        solver->mkTupleSelect(outer, 1), 1))),
      solver->mkEqual(solver->mkTupleSelect(newOuter, 0),
                      solver->mkTupleSelect(outer, 0)));
  solver->addConstraint(solver->mkNot(ok));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Model extraction through an update.
  solver->reset();
  bv8Sort = solver->mkBVSort(8);
  auto pairSort = solver->mkTupleSort({bv8Sort, bv8Sort});
  auto p = solver->mkSymbol("p", pairSort);
  auto q = solver->mkTupleUpdate(p, 0, solver->mkBVFromDec(11, 8));
  solver->addConstraint(
      solver->mkEqual(solver->mkTupleSelect(p, 1), solver->mkBVFromDec(5, 8)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto f0 = solver->getBV(solver->mkTupleSelect(q, 0));
  REQUIRE(f0);
  REQUIRE(f0.value() == 11);
  auto f1 = solver->getBV(solver->mkTupleSelect(q, 1));
  REQUIRE(f1);
  REQUIRE(f1.value() == 5);
}

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
