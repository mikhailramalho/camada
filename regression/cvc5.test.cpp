
#include "smtlib_pipeline.test.h"
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <cvc5solver.h>

TEST_CASE("Simple CVC5 test", "[CVC5]") {
  // Create CVC5 Solver
  auto cvc5 = camada::createCVC5Solver();
  tests(cvc5);
}

TEST_CASE("Quantifiers CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  quantifier_semantics(cvc5);
}

TEST_CASE("UF CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  uf_semantics(cvc5);
}

TEST_CASE("Arith CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  int_arithmetic_semantics(cvc5);
  cvc5->reset();
  real_arithmetic_semantics(cvc5);
  cvc5->reset();
  arith_model_queries(cvc5);
  cvc5->reset();
  arith_conversion_semantics(cvc5);
  cvc5->reset();
  arith_symbolic_shift_semantics(cvc5);
}

TEST_CASE("Tuple CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  tuple_semantics(cvc5);
}

TEST_CASE("Empty tuple CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  empty_tuple_semantics(cvc5);
}

// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the cvc5 binary. cvc5 supports the full
// Camada surface (BV, Bool, arrays, FP-native, FP-BV, Int, Real, UF,
// quantifiers, tuples). Same coverage as the z3 pipeline tests.
// ---------------------------------------------------------------------------

#define CAMADA_CVC5_SMTLIB_PIPELINE_TEST(NameStr, RunFn)                       \
  TEST_CASE("SMTLIB pipeline: " NameStr " [cvc5]",                             \
            "[CVC5][SMTLIB][pipeline]") {                                      \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::cvc5Command(),        \
                                 "cvc5");                                      \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_CVC5_SMTLIB_PIPELINE_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_CVC5_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                                 runSMTLIBDualEmitter)
CAMADA_CVC5_SMTLIB_PIPELINE_TEST(
    "getBVInBin handles 128-bit decimal model value", runSMTLIBGetBVInBin128)
CAMADA_CVC5_SMTLIB_PIPELINE_TEST("native FP infinity model parses",
                                 runSMTLIBNativeFPInfinity)
CAMADA_CVC5_SMTLIB_PIPELINE_TEST("native FP NaN model parses",
                                 runSMTLIBNativeFPNaNModel)
CAMADA_CVC5_SMTLIB_PIPELINE_TEST("native FP neg FlipSignBit toggles NaN sign",
                                 runSMTLIBNativeFPNegFlipNaN)

#undef CAMADA_CVC5_SMTLIB_PIPELINE_TEST

#define CAMADA_CVC5_SMTLIB_SHARED_TEST(NameStr, FixtureCall)                   \
  TEST_CASE("SMTLIB pipeline: " NameStr " [cvc5]",                             \
            "[CVC5][SMTLIB][pipeline]") {                                      \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::cvc5Command(),        \
                                 "cvc5");                                      \
    camada::SMTSolverRef solver =                                              \
        camada_smtlib_pipeline::makeSMTLIBSolver(Cmd);                         \
    FixtureCall;                                                               \
  }

CAMADA_CVC5_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("implies_semantics", implies_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("implies_true_implies_false",
                               implies_true_implies_false(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("bv_lshr_semantics", bv_lshr_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("incremental_push_pop",
                               incremental_push_pop(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                               symbol_cache_survives_push_pop(solver))
// Array fixtures and arith_model_queries are absent: cvc5 over the SMT-LIB
// pipe with `(set-logic ALL)` returns `unknown` for these formulas (the array
// + arith reasoning paths it picks under ALL differ from the native API
// path). Those are real cvc5 quirks that the pipeline can't paper over.
CAMADA_CVC5_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("quantifier_semantics",
                               quantifier_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("int_arithmetic_semantics",
                               int_arithmetic_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("real_arithmetic_semantics",
                               real_arithmetic_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("arith_conversion_semantics",
                               arith_conversion_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("tuple_semantics", tuple_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("empty_tuple_semantics",
                               empty_tuple_semantics(solver))
CAMADA_CVC5_SMTLIB_SHARED_TEST("fp_equal NativeFP",
                               fp_equal(solver, camada::FPEncoding::Native))
CAMADA_CVC5_SMTLIB_SHARED_TEST("fp_equal BVFP",
                               fp_equal(solver, camada::FPEncoding::BV))

#undef CAMADA_CVC5_SMTLIB_SHARED_TEST
