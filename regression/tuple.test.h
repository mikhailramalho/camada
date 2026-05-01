
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
