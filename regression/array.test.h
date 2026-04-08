
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
  REQUIRE(selected->Sort == elemsort);
  REQUIRE(solver->getBVInBin(selected) == "0000001010");
}

inline void array_const_store_semantics(const camada::SMTSolverRef &solver) {
  auto indexsort = solver->mkBVSort(3);
  auto elemsort = solver->mkBVSort(8);

  auto init = solver->mkBVFromDec(170, elemsort);
  auto stored = solver->mkBVFromDec(17, elemsort);
  auto idx_written = solver->mkBVFromDec(3, indexsort);
  auto idx_other = solver->mkBVFromDec(5, indexsort);

  auto arr = solver->mkArrayConst(indexsort, init);
  auto updated = solver->mkArrayStore(arr, idx_written, stored);

  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_written), stored));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_other), init));

  REQUIRE(solver->check() == camada::checkResult::SAT);

  auto read_written = solver->getArrayElement(updated, idx_written);
  auto read_other = solver->getArrayElement(updated, idx_other);

  REQUIRE(read_written->Sort == elemsort);
  REQUIRE(read_other->Sort == elemsort);
  REQUIRE(solver->getBVInBin(read_written) == "00010001");
  REQUIRE(solver->getBVInBin(read_other) == "10101010");
}

inline void
bool_array_const_store_semantics(const camada::SMTSolverRef &solver) {
  auto indexsort = solver->mkBVSort(2);
  auto boolsort = solver->mkBoolSort();

  auto init = solver->mkBool(false);
  auto stored = solver->mkBool(true);
  auto idx_written = solver->mkBVFromDec(1, indexsort);
  auto idx_other = solver->mkBVFromDec(2, indexsort);

  auto arr = solver->mkArrayConst(indexsort, init);
  REQUIRE(arr->getKind() == camada::SMTExprKind::ArrayConst);
  REQUIRE(arr->Sort->getElementSort() == boolsort);

  auto updated = solver->mkArrayStore(arr, idx_written, stored);
  REQUIRE(updated->getKind() == camada::SMTExprKind::ArrayStore);
  REQUIRE(updated->Sort->getElementSort() == boolsort);

  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_written), stored));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_other), init));

  REQUIRE(solver->check() == camada::checkResult::SAT);

  auto read_written = solver->getArrayElement(updated, idx_written);
  auto read_other = solver->getArrayElement(updated, idx_other);

  REQUIRE(read_written->Sort == boolsort);
  REQUIRE(read_other->Sort == boolsort);
  REQUIRE(solver->getBool(read_written));
  REQUIRE(!solver->getBool(read_other));
}
