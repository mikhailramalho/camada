
#include "array.test.h"
#include "fp.test.h"
#include "simple.test.h"
#include "tuple.test.h"

#include <catch2/catch_test_macros.hpp>

#define RESETANDTEST(testname)                                                 \
  solver->reset();                                                             \
  testname(solver);

#define RESETANDFPTEST(testname, encoding)                                     \
  solver->reset();                                                             \
  testname(solver, encoding);

inline void tests(const camada::SMTSolverRef &solver) {
  constexpr auto NativeFP = camada::FPEncoding::Native;
  constexpr auto BVFP = camada::FPEncoding::BV;

  RESETANDTEST(equal_ten);
  RESETANDTEST(implies_semantics);
  RESETANDTEST(implies_true_implies_false);
  RESETANDTEST(bv_lshr_semantics);
  RESETANDTEST(incremental_push_pop);
  RESETANDTEST(array);
  RESETANDTEST(array_const_store_semantics);
  RESETANDTEST(bool_array_const_store_semantics);
  RESETANDTEST(dump_string_semantics);
  RESETANDFPTEST(fp_equal, NativeFP);
  RESETANDFPTEST(fp_equal, BVFP);
  RESETANDFPTEST(fp_arithmetics, NativeFP);
  RESETANDFPTEST(fp_arithmetics, BVFP);
  RESETANDFPTEST(fp_round_to_away, NativeFP);
  RESETANDFPTEST(fp_round_to_away, BVFP);
  RESETANDFPTEST(fp_bv_conversions, NativeFP);
  RESETANDFPTEST(fp_bv_conversions, BVFP);
  RESETANDFPTEST(fp_denormal_round_to_integral, NativeFP);
  RESETANDFPTEST(fp_denormal_round_to_integral, BVFP);
  RESETANDFPTEST(fp_div_overflow_to_inf, NativeFP);
  RESETANDFPTEST(fp_div_overflow_to_inf, BVFP);
  RESETANDFPTEST(fp_remainder_semantics, NativeFP);
  RESETANDFPTEST(fp_remainder_semantics, BVFP);
}
