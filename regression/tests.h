
#include "ackarray.test.h"
#include "array.test.h"
#include "fp.test.h"
#include "fxp.test.h"
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

// Degenerate formats whose significand cannot be renormalized within the
// exponent arithmetic width are rejected at sort creation for the BV
// encoding (they would silently misround; see mkFPSort). Lives here
// rather than fp.test.h because it needs require_abort.
inline void fp_degenerate_format_rejected(const camada::SMTSolverRef &solver) {
  require_abort(
      [&]() { (void)solver->mkFPSort(2, 10, camada::FPEncoding::BV); });
  // The boundary format itself is accepted: 2*(4+1)+5 = 15 = 2^(3+1)-1.
  auto ok = solver->mkFPSort(3, 4, camada::FPEncoding::BV);
  REQUIRE(ok->isFPSort());
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
  RESETANDTEST(lazy_array_transitive_equality);
  RESETANDARGTEST(lazy_array_transitive_equality, LazyArrays);
  RESETANDTEST(array_equality_witness_congruence);
  RESETANDTEST(lazy_array_equality_reached_defaults);
  RESETANDARGTEST(lazy_array_equality_reached_defaults, LazyArrays);
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
  RESETANDARGTEST(fp_ieee_bv_sort_identity, NativeFP);
  RESETANDARGTEST(fp_ieee_bv_sort_identity, BVFP);
  RESETANDARGTEST(fp_ieee_bv_bitexact_roundtrip, NativeFP);
  RESETANDARGTEST(fp_ieee_bv_bitexact_roundtrip, BVFP);
  RESETANDARGTEST(fp_ieee_bv_consistency, NativeFP);
  RESETANDARGTEST(fp_ieee_bv_consistency, BVFP);
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
  RESETANDTEST(fp_wide_format_semantics);
  RESETANDTEST(fp_degenerate_format_rejected);

  // Fixed-point: pure common-layer BV encoding, no backend gating needed.
  RESETANDTEST(fxp_exhaustive_semantics);
  RESETANDTEST(fxp_boundary_overflow_semantics);
  RESETANDTEST(fxp_rounding_semantics);
  RESETANDTEST(fxp_conversion_matrix);
  RESETANDTEST(fxp_mixed_format_semantics);
  RESETANDTEST(fxp_shift_semantics);
  RESETANDTEST(fxp_model_and_constructs);
  RESETANDTEST(fxp_sat_exhaustive_semantics);
  RESETANDTEST(fxp_sat_shift_semantics);
  RESETANDTEST(fxp_sat_conversion_semantics);
}
