
#include "camada.h"

#include <bitset>
#include <catch2/catch.hpp>

inline void array(const camada::SMTSolverRef &solver) {
  // An array
  auto indexsort = solver->mkBVSort(2);
  auto elemsort = solver->mkBVSort(10);
  auto arr = solver->mkArrayConst(indexsort, solver->mkBVFromDec(5, 10));

  auto arr1 = solver->mkSymbol("f1", solver->mkArraySort(indexsort, elemsort));
  auto arr11 = solver->mkArrayStore(arr1, solver->mkBVFromDec(1, 2),
                                    solver->mkBVFromDec(10, 10));
  auto eq = solver->mkNot(solver->mkEqual(arr, arr11));

  // Add the constraint to the solver, And check for satisfiability
  solver->addConstraint(eq);
  REQUIRE(solver->check() == camada::checkResult::SAT);
  REQUIRE(solver->getBVInBin(solver->getArrayElement(
              arr11, solver->mkBVFromDec(1, 2))) == "0000001010");
}
