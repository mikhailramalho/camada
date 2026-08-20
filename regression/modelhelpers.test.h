
#pragma once
#include "camada.h"

#include <catch2/catch_test_macros.hpp>

/// Unwrap a model getter that reports failure through SMTResult, failing the
/// test rather than aborting when the backend could not answer. Tests that
/// care about the error path check the SMTResult directly instead.
inline camada::SMTExprRef arrayElement(const camada::SMTSolverRef &solver,
                                       const camada::SMTExprRef &Array,
                                       const camada::SMTExprRef &Index) {
  camada::SMTResult<camada::SMTExprRef> Element =
      solver->getArrayElement(Array, Index);
  REQUIRE(Element);
  return Element.value();
}
