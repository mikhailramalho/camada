
#include <catch2/catch_test_macros.hpp>

inline void tuple_semantics(const camada::SMTSolverRef &solver) {
  auto boolSort = solver->mkBoolSort();
  auto bv8Sort = solver->mkBVSort(8);
  auto intSort = solver->mkIntSort();
  auto tupleSort = solver->mkTupleSort({boolSort, bv8Sort, intSort});

  REQUIRE(tupleSort->isTupleSort());
  REQUIRE(tupleSort->getTupleElementSorts().size() == 3);
  REQUIRE(tupleSort->getTupleElementSorts()[0] == boolSort);
  REQUIRE(tupleSort->getTupleElementSorts()[1] == bv8Sort);
  REQUIRE(tupleSort->getTupleElementSorts()[2] == intSort);

  auto tupleValue = solver->mkTuple(
      {solver->mkBool(true), solver->mkBVFromDec(42, 8), solver->mkInt(7)});
  REQUIRE(tupleValue->getKind() == camada::SMTExprKind::TupleConst);

  auto tupleSymbol = solver->mkSymbol("t", tupleSort);
  solver->addConstraint(solver->mkEqual(tupleSymbol, tupleValue));

  auto b = solver->mkTupleSelect(tupleSymbol, 0);
  auto bv = solver->mkTupleSelect(tupleSymbol, 1);
  auto i = solver->mkTupleSelect(tupleSymbol, 2);

  REQUIRE(b->getKind() == camada::SMTExprKind::TupleSelect);
  REQUIRE(bv->getKind() == camada::SMTExprKind::TupleSelect);
  REQUIRE(i->getKind() == camada::SMTExprKind::TupleSelect);
  REQUIRE(b->Sort == boolSort);
  REQUIRE(bv->Sort == bv8Sort);
  REQUIRE(i->Sort == intSort);

  solver->addConstraint(solver->mkEqual(b, solver->mkBool(true)));
  solver->addConstraint(solver->mkEqual(bv, solver->mkBVFromDec(42, 8)));
  solver->addConstraint(solver->mkEqual(i, solver->mkInt(7)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}
