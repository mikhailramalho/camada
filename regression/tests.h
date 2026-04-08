
#include "array.test.h"
#include "fp.test.h"
#include "simple.test.h"
#include "tuple.test.h"

#include <catch2/catch_test_macros.hpp>
#include <csignal>
#include <cstdlib>
#include <sys/wait.h>
#include <unistd.h>

#define RESETANDTEST(testname)                                                 \
  solver->reset();                                                             \
  testname(solver);

#define RESETANDFPTEST(testname, encoding)                                     \
  solver->reset();                                                             \
  testname(solver, encoding);

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
  RESETANDTEST(incremental_push_pop);
  RESETANDTEST(handle_invalidation_after_reset);
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
  RESETANDFPTEST(fp_to_signed_bv_multiple_widths, BVFP);
  RESETANDFPTEST(fp_denormal_round_to_integral, NativeFP);
  RESETANDFPTEST(fp_denormal_round_to_integral, BVFP);
  RESETANDFPTEST(fp_div_overflow_to_inf, NativeFP);
  RESETANDFPTEST(fp_div_overflow_to_inf, BVFP);
  RESETANDFPTEST(fp_remainder_semantics, NativeFP);
  RESETANDFPTEST(fp_remainder_semantics, BVFP);
}
