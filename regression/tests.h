
#include "array.test.h"
#include "fp.test.h"
#include "simple.test.h"

#include <catch2/catch.hpp>

#define RESETANDTEST(testname)                                                 \
  solver->reset();                                                             \
  testname(solver);

inline void tests(const camada::SMTSolverRef &solver) {
  RESETANDTEST(equal_ten);
  RESETANDTEST(fp_equal);
  RESETANDTEST(array);
  RESETANDTEST(fp_arithmetics);
}
