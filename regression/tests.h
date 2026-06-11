
#include "array.test.h"
#include "fp.test.h"
#include "simple.test.h"
#include "tuple.test.h"

#include <catch2/catch_test_macros.hpp>
#include <csignal>
#include <cstdlib>
#if !defined(_WIN32)
#include <sys/wait.h>
#include <unistd.h>
#endif

#define RESETANDTEST(testname)                                                 \
  solver->reset();                                                             \
  testname(solver);

#define RESETANDARGTEST(testname, arg)                                         \
  solver->reset();                                                             \
  testname(solver, arg);

template <typename Fn> inline void require_abort(Fn &&Body) {
#if defined(_WIN32)
  SKIP("Abort regression helper is not implemented on Windows");
#else
  const pid_t pid = fork();
  REQUIRE(pid != -1);

  if (pid == 0) {
    Body();
    std::_Exit(0);
  }

  int status = 0;
  REQUIRE(waitpid(pid, &status, 0) == pid);
  REQUIRE(WIFSIGNALED(status));
  REQUIRE(WTERMSIG(status) == SIGABRT);
#endif
}

inline void tests(const camada::SMTSolverRef &solver) {
  constexpr auto NativeFP = camada::FPEncoding::Native;
  constexpr auto BVFP = camada::FPEncoding::BV;

  RESETANDTEST(equal_ten);
  RESETANDTEST(implies_semantics);
  RESETANDTEST(implies_true_implies_false);
  RESETANDTEST(bv_lshr_semantics);
  RESETANDTEST(bv_overflow_semantics);
  RESETANDTEST(solver_timeout_semantics);

  RESETANDTEST(check_sat_assuming_semantics);
  RESETANDTEST(narrow_bv_decimal_model_value);
  RESETANDTEST(shared_subterm_model_value);
  RESETANDTEST(wide_bv_decimal_model_value);
  RESETANDTEST(incremental_push_pop);
  RESETANDTEST(symbol_cache_survives_push_pop);
  RESETANDTEST(handle_invalidation_after_reset);
  RESETANDTEST(array);
  RESETANDTEST(array_const_store_semantics);
  RESETANDTEST(bool_array_const_store_semantics);
  RESETANDTEST(array_const_survives_push_pop);
  RESETANDTEST(wide_index_const_array_semantics);
  RESETANDTEST(const_array_select_survives_pop);
  RESETANDTEST(array_equality_semantics);
  RESETANDTEST(const_array_equality_semantics);
  constexpr auto LazyArrays = camada::ConstArrayLowering::Lazy;
  RESETANDARGTEST(array, LazyArrays);
  RESETANDARGTEST(array_const_store_semantics, LazyArrays);
  RESETANDARGTEST(bool_array_const_store_semantics, LazyArrays);
  RESETANDARGTEST(array_const_survives_push_pop, LazyArrays);
  RESETANDARGTEST(wide_index_const_array_semantics, LazyArrays);
  RESETANDARGTEST(const_array_select_survives_pop, LazyArrays);
  RESETANDARGTEST(const_array_equality_semantics, LazyArrays);
  RESETANDTEST(array_model_values);
  RESETANDTEST(const_array_model_values);
  RESETANDARGTEST(const_array_model_values, LazyArrays);
  RESETANDTEST(const_array_lowering_interop);
  RESETANDTEST(tuple_semantics);
  RESETANDTEST(tuple_with_array_field);
  RESETANDTEST(tuple_update_semantics);
  RESETANDTEST(tuple_structural_equality);
  RESETANDTEST(tuple_array_semantics);
  RESETANDTEST(tuple_array_equality_ite);
  RESETANDTEST(tuple_array_const);
  RESETANDARGTEST(tuple_array_const, LazyArrays);
  RESETANDTEST(tuple_array_model_values);
  RESETANDARGTEST(tuple_array_model_values, LazyArrays);
  RESETANDTEST(empty_tuple_semantics);
  RESETANDTEST(dump_string_semantics);
  RESETANDTEST(fp_native_bv_predicate_parity);
  RESETANDTEST(fp_neg_nan_native_bv_parity);
  RESETANDARGTEST(fp_equal, NativeFP);
  RESETANDARGTEST(fp_equal, BVFP);
  RESETANDARGTEST(fp_infinity_model_value, NativeFP);
  RESETANDARGTEST(fp_nan_model_value, NativeFP);
  RESETANDARGTEST(fp_neg_flip_nan_via_bv_round_trip, BVFP);
  RESETANDARGTEST(fp_arithmetics, NativeFP);
  RESETANDARGTEST(fp_arithmetics, BVFP);
  RESETANDARGTEST(fp_round_to_away, NativeFP);
  RESETANDARGTEST(fp_round_to_away, BVFP);
  RESETANDARGTEST(fp_bv_conversions, NativeFP);
  RESETANDARGTEST(fp_bv_conversions, BVFP);
  RESETANDARGTEST(fp_to_signed_bv_multiple_widths, BVFP);
  RESETANDARGTEST(fp_denormal_round_to_integral, NativeFP);
  RESETANDARGTEST(fp_denormal_round_to_integral, BVFP);
  RESETANDARGTEST(fp_div_overflow_to_inf, NativeFP);
  RESETANDARGTEST(fp_div_overflow_to_inf, BVFP);
  RESETANDARGTEST(fp_remainder_semantics, NativeFP);
  RESETANDARGTEST(fp_remainder_semantics, BVFP);
  RESETANDARGTEST(fp_remainder_host_oracle, NativeFP);
  RESETANDARGTEST(fp_remainder_host_oracle, BVFP);
  RESETANDTEST(arena_stress_test);
  RESETANDARGTEST(fp_non_standard_widths, BVFP);
  RESETANDARGTEST(fp_cancellation_and_normalization, NativeFP);
  RESETANDARGTEST(fp_cancellation_and_normalization, BVFP);
}
