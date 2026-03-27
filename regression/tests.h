
#include "array.test.h"
#include "fp.test.h"
#include "simple.test.h"

#include <catch2/catch_test_macros.hpp>

#define RESETANDTEST(testname)                                                 \
  solver->reset();                                                             \
  testname(solver);

inline void tests(const camada::SMTSolverRef &solver) {
  RESETANDTEST(equal_ten);
  RESETANDTEST(implies_semantics);
  RESETANDTEST(implies_true_implies_false);
  RESETANDTEST(bv_lshr_semantics);
  RESETANDTEST(incremental_push_pop);
  RESETANDTEST(fp_equal);
  RESETANDTEST(array);
  RESETANDTEST(array_const_store_semantics);
  RESETANDTEST(bool_array_const_store_semantics);
  RESETANDTEST(dump_string_semantics);
  RESETANDTEST(fp_arithmetics);
  RESETANDTEST(fp_round_to_away);
  RESETANDTEST(fp_bv_conversions);
  RESETANDTEST(fp_denormal_round_to_integral);
  RESETANDTEST(fp_div_overflow_to_inf);
  RESETANDTEST(fp_remainder_semantics);
}
