
#include "camada.h"

#include <bitset>
#include <catch2/catch_test_macros.hpp>

inline void array(const camada::SMTSolverRef &solver) {
  // An array
  auto indexsort = solver->mkBVSort(2);
  auto elemsort = solver->mkBVSort(10);
  auto init = solver->mkBVFromDec(5, 10);
  REQUIRE(init->getKind() == camada::SMTExprKind::BVConst);
  auto arr = solver->mkArrayConst(indexsort, init);
  REQUIRE(arr->getKind() == camada::SMTExprKind::ArrayConst);

  auto arr1 = solver->mkSymbol("f1", solver->mkArraySort(indexsort, elemsort));
  REQUIRE(arr1->getKind() == camada::SMTExprKind::Symbol);
  auto index = solver->mkBVFromDec(1, 2);
  auto element = solver->mkBVFromDec(10, 10);
  REQUIRE(index->getKind() == camada::SMTExprKind::BVConst);
  REQUIRE(element->getKind() == camada::SMTExprKind::BVConst);
  auto arr11 = solver->mkArrayStore(arr1, index, element);
  REQUIRE(arr11->getKind() == camada::SMTExprKind::ArrayStore);
  auto neq = solver->mkEqual(arr, arr11);
  REQUIRE(neq->getKind() == camada::SMTExprKind::Equal);
  auto eq = solver->mkNot(neq);
  REQUIRE(eq->getKind() == camada::SMTExprKind::Not);

  // Add the constraint to the solver, And check for satisfiability
  solver->addConstraint(eq);
  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto selected = solver->getArrayElement(arr11, solver->mkBVFromDec(1, 2));
  REQUIRE(selected->getKind() == camada::SMTExprKind::ArraySelect);
  REQUIRE(solver->getBVInBin(selected) == "0000001010");
}
