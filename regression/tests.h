
#include "ackarray.test.h"
#include "array.test.h"
#include "bvconformance.test.h"
#include "fp.test.h"
#include "fpconformance.test.h"
#include "fxp.test.h"
#include "fxporacle.test.h"
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
// A leading-sign count needs a target wide enough to hold it; a narrower
// one would silently truncate. Lives here because it needs require_abort.
inline void
fxp_countls_narrow_target_rejected(const camada::SMTSolverRef &solver) {
  auto s64 = solver->mkFXPSort(64, 31, true);
  auto x = solver->mkSymbol("fxp_cls_narrow", s64);
  require_abort([&]() { (void)solver->mkFXPCountls(x, 4); });
  // Six bits hold 63, the largest count for this format.
  REQUIRE(solver->mkFXPCountls(x, 6)->getWidth() == 6);
}

// A handle only means anything to the solver that made it: passing one to
// another instance used to reach the backend, where it was static_cast to
// that backend's type. Observed in release builds as an uncaught
// z3::exception between two Z3 instances and a segfault when a Yices term
// reached Z3. Lives here because it needs require_abort.
inline void foreign_handle_rejected(const camada::SMTSolverRef &solver,
                                    const camada::SMTSolverRef &other) {
#if !CAMADA_CHECKED_HANDLES
  // Unchecked handles carry no owner, so a foreign one cannot be detected
  // and its use stays undefined behavior by contract.
  (void)solver;
  (void)other;
  SKIP("foreign-handle detection is compiled out (CAMADA_CHECKED_HANDLES=OFF)");
#else
  auto mine = solver->mkSymbol("own", solver->mkBVSort(8));
  auto theirs = other->mkSymbol("foreign", other->mkBVSort(8));

  // As an operand, on either side of the operation.
  require_abort([&]() { (void)solver->mkBVAdd(theirs, mine); });
  require_abort([&]() { (void)solver->mkBVAdd(mine, theirs); });
  require_abort([&]() { (void)solver->mkBVNot(theirs); });
  require_abort([&]() { (void)solver->mkEqual(theirs, mine); });

  // As a constraint, and as the subject of a model query.
  require_abort(
      [&]() { solver->addConstraint(other->mkEqual(theirs, theirs)); });

  // Sort parameters route through no operand guard, so check one.
  require_abort([&]() { (void)solver->mkSymbol("s", other->mkBVSort(4)); });
  require_abort([&]() {
    (void)solver->mkArraySort(other->mkBVSort(4), solver->mkBVSort(4));
  });

  // The solver's own handles keep working after all that.
  solver->addConstraint(solver->mkEqual(mine, solver->mkBVFromDec(7, 8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  auto v = solver->getBV(mine);
  REQUIRE(v);
  REQUIRE(v.value() == 7);
#endif
}

inline void pop_past_root_rejected(const camada::SMTSolverRef &solver) {
  // Each check runs in a forked child, so the abort does not take the
  // test process with it and the parent's scope depth is untouched.
  require_abort([&]() { solver->pop(1); });
  solver->push(1);
  require_abort([&]() { solver->pop(2); });
  solver->pop(1);
  auto x = solver->mkSymbol("pop_x", solver->mkBVSort(4));
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(1, 4)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// getRM on a non-rounding-mode expression is a usage error. Lives here
// because it needs require_abort.
inline void rm_getter_rejects_non_rm(const camada::SMTSolverRef &solver) {
  auto bv = solver->mkSymbol("not_rm", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(bv, solver->mkBVFromDec(1, 8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  require_abort([&]() { (void)solver->getRM(bv); });
}

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
  RESETANDTEST(symbol_name_punctuation_distinct);
  RESETANDTEST(null_sort_handle_equality);
  RESETANDTEST(bv_typed_getter_domain);
  RESETANDTEST(pop_underflow_rejected);
  RESETANDTEST(pop_past_root_rejected);
  RESETANDTEST(implies_semantics);
  RESETANDTEST(implies_true_implies_false);
  RESETANDTEST(bv_lshr_semantics);
  RESETANDTEST(bv_extend_by_zero_semantics);
  RESETANDTEST(bv_signed_div_rem_semantics);
  RESETANDTEST(bv_conformance_semantics);
  RESETANDTEST(fxp_gap_conformance);
  RESETANDARGTEST(fp_conformance_semantics, NativeFP);
  RESETANDARGTEST(fp_conformance_semantics, BVFP);
  RESETANDTEST(bv_overflow_semantics);
  RESETANDTEST(unknown_reason_semantics);
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
  RESETANDTEST(fp_neg_nan_payload_bits);
  RESETANDTEST(fp_nan_payload_propagation);
  RESETANDTEST(fp_sort_width_accessors);
  RESETANDARGTEST(rm_model_value, NativeFP);
  RESETANDARGTEST(rm_model_value, BVFP);
  RESETANDTEST(rm_getter_rejects_non_rm);
  RESETANDARGTEST(fp_typed_getter_format, NativeFP);
  RESETANDARGTEST(fp_typed_getter_format, BVFP);
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
  RESETANDARGTEST(fp_addsub_host_oracle, NativeFP);
  RESETANDARGTEST(fp_addsub_host_oracle, BVFP);
  RESETANDARGTEST(fp_sqrt_host_oracle, NativeFP);
  RESETANDARGTEST(fp_sqrt_host_oracle, BVFP);
  RESETANDARGTEST(fp_fma_host_oracle, NativeFP);
  RESETANDARGTEST(fp_fma_host_oracle, BVFP);
  RESETANDARGTEST(fp_muldiv_subnormal_host_oracle, NativeFP);
  RESETANDARGTEST(fp_muldiv_subnormal_host_oracle, BVFP);
  RESETANDARGTEST(fp_tointegral_large_values, NativeFP);
  RESETANDARGTEST(fp_tointegral_large_values, BVFP);
  RESETANDTEST(fp_tointegral_large_values_bv);
  RESETANDARGTEST(fp_remainder_host_oracle, NativeFP);
  RESETANDARGTEST(fp_remainder_host_oracle, BVFP);
  RESETANDTEST(arena_stress_test);
  RESETANDARGTEST(fp_non_standard_widths, BVFP);
  RESETANDARGTEST(fp_cancellation_and_normalization, NativeFP);
  RESETANDARGTEST(fp_cancellation_and_normalization, BVFP);
  RESETANDTEST(fp_wide_format_semantics);
  RESETANDTEST(fp_degenerate_format_rejected);
  RESETANDTEST(fxp_countls_narrow_target_rejected);

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
  RESETANDTEST(fxp_symbolic_shift_semantics);
  RESETANDTEST(fxp_abs_countls_semantics);
  RESETANDTEST(fxp_sqrt_semantics);
  RESETANDTEST(fxp_exp_semantics);
  RESETANDTEST(fxp_round_semantics);
  RESETANDTEST(fxp_oracle_semantics);
  RESETANDTEST(fxp_oracle_mixed_semantics);
  RESETANDARGTEST(fxp_fp_conversion_semantics, NativeFP);
  RESETANDARGTEST(fxp_fp_conversion_semantics, BVFP);
}
