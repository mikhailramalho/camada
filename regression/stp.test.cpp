
#if SOLVER_SMTLIB_ENABLED
#include "smtlib_pipeline.test.h"
#endif
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <stpsolver.h>

TEST_CASE("Ackermann arrays STP test", "[STP]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto stp = camada::createSTPSolver(Cfg);
  ack_array_tests(stp);
}

TEST_CASE("Simple STP test", "[STP]") {
  // Create STP Solver
  auto stp = camada::createSTPSolver();
  tests(stp);
}

TEST_CASE("Unsupported UF STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    auto fn = stp->mkFunctionSort({bv4}, bv4);
    (void)stp->mkSymbol("f", fn);
  });
}

TEST_CASE("STP feature capabilities", "[STP]") {
  auto solver = camada::createSTPSolver();
  using camada::SolverFeature;
  REQUIRE_FALSE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE_FALSE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE_FALSE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE_FALSE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE_FALSE(solver->supports(SolverFeature::ArrayModels));
}

TEST_CASE("Unsupported nested arrays STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    (void)stp->mkArraySort(bv4, stp->mkArraySort(bv4, bv4));
  });
}

TEST_CASE("Unsupported tuple-array UF/quantifier boundaries STP test",
          "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    auto tupArr = stp->mkArraySort(bv4, stp->mkTupleSort({bv4}));
    (void)stp->mkFunctionSort({tupArr}, bv4);
  });
}

TEST_CASE("Unsupported nested constant tuple arrays STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    auto init = stp->mkTuple({stp->mkBool(true), stp->mkBVFromDec(5, 8)});
    auto innerConst = stp->mkArrayConst(bv4, init);
    (void)stp->mkArrayConst(bv4, innerConst);
  });
}
#if SOLVER_SMTLIB_ENABLED
// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the stp binary (STP >= 2.4.0, which answers
// the SMT-LIB2 commands it does not implement instead of dying). stp supports
// BV, Bool, plain arrays, and FP-BV (via bit-blast). It rejects
// (set-logic ALL) — the preamble falls back to QF_AUFBV — and answers
// `unsupported` to :global-declarations, :produce-unsat-assumptions, and
// (check-sat-assuming ...), so checkSatAssuming routes through the common
// push/assert/check/pop fallback and symbols declared inside a (push) die
// with their scope (symbol_cache_survives_push_pop is therefore absent).
// Array fixtures are absent for the same reasons as yices-smt2: they all use
// `mkArrayConst`, and stp additionally rejects `((as const ...))` syntax and
// (get-value ...) on compound terms.
// ---------------------------------------------------------------------------

#define CAMADA_STP_SMTLIB_PIPELINE_TEST(NameStr, RunFn)                        \
  TEST_CASE("SMTLIB pipeline: " NameStr " [stp]", "[STP][SMTLIB][pipeline]") { \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::stpCommand(), "stp"); \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_STP_SMTLIB_PIPELINE_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_STP_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                                runSMTLIBDualEmitter)

#undef CAMADA_STP_SMTLIB_PIPELINE_TEST

#define CAMADA_STP_SMTLIB_SHARED_TEST(NameStr, FixtureCall)                    \
  TEST_CASE("SMTLIB pipeline: " NameStr " [stp]", "[STP][SMTLIB][pipeline]") { \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::stpCommand(), "stp"); \
    camada::SMTSolverRef solver =                                              \
        camada_smtlib_pipeline::makeSMTLIBSolver(Cmd);                         \
    FixtureCall;                                                               \
  }

CAMADA_STP_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver))
CAMADA_STP_SMTLIB_SHARED_TEST("implies_semantics", implies_semantics(solver))
CAMADA_STP_SMTLIB_SHARED_TEST("implies_true_implies_false",
                              implies_true_implies_false(solver))
CAMADA_STP_SMTLIB_SHARED_TEST("check_sat_assuming_semantics",
                              check_sat_assuming_semantics(solver))
CAMADA_STP_SMTLIB_SHARED_TEST("bv_lshr_semantics", bv_lshr_semantics(solver))
CAMADA_STP_SMTLIB_SHARED_TEST("incremental_push_pop",
                              incremental_push_pop(solver))
CAMADA_STP_SMTLIB_SHARED_TEST("fp_equal BVFP",
                              fp_equal(solver, camada::FPEncoding::BV))

CAMADA_STP_SMTLIB_SHARED_TEST("fxp_rounding_semantics",
                              fxp_rounding_semantics(solver))
CAMADA_STP_SMTLIB_SHARED_TEST("fxp_model_and_constructs",
                              fxp_model_and_constructs(solver))

#undef CAMADA_STP_SMTLIB_SHARED_TEST

// The Ackermann array encoding is aimed exactly at solvers like STP,
// whose array support is its weakest theory: with it, the wire carries
// no array sorts or select/store terms at all. checkSatAssuming inside
// the fixture exercises the push/assert/check/pop fallback (the STP
// child has no unsat-assumptions support), which replays the journaled
// congruence axioms. Only the flat driver runs here: stp answers
// `unsupported` to `:global-declarations true`, so fixtures that mint
// read variables inside a (push) scope hit the documented
// scoped-declaration limitation of such children.
TEST_CASE("SMTLIB pipeline: ack_array_tests_flat [Ackermann] [stp]",
          "[STP][SMTLIB][pipeline]") {
  CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::stpCommand(), "stp");
  camada::SMTSolverRef solver =
      camada_smtlib_pipeline::makeSMTLIBSolverAckermannArrays(Cmd);
  ack_array_tests_flat(solver);
}
#endif

TEST_CASE("Unsupported nested constant arrays STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() { nested_const_array_semantics(stp); });
}
