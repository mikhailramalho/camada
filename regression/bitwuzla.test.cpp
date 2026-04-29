
#include "smtlib_pipeline.test.h"
#include "tests.h"

#include <bitwuzlasolver.h>
#include <catch2/catch_test_macros.hpp>

TEST_CASE("Simple Bitwuzla test", "[Bitwuzla]") {
  auto bitwuzla = camada::createBitwuzlaSolver();
  tests(bitwuzla);
}

TEST_CASE("Quantifiers Bitwuzla test", "[Bitwuzla]") {
  auto bitwuzla = camada::createBitwuzlaSolver();
  quantifier_semantics(bitwuzla);
}

TEST_CASE("UF Bitwuzla test", "[Bitwuzla]") {
  auto bitwuzla = camada::createBitwuzlaSolver();
  uf_semantics(bitwuzla);
}

TEST_CASE("Unsupported arithmetic Bitwuzla test", "[Bitwuzla]") {
  auto bitwuzla = camada::createBitwuzlaSolver();
  require_abort([&]() { (void)bitwuzla->mkIntSort(); });
}

TEST_CASE("Override Bitwuzla Solver", "[Bitwuzla]") {

  class myBitwuzlaSolver : public camada::BitwuzlaSolver {
  public:
    explicit myBitwuzlaSolver() { reset(); }

    void resetImpl() override {
      destroyContext();
      initializeContext();
    }
  };

  camada::SMTSolverRef bitwuzla = std::make_unique<myBitwuzlaSolver>();
  tests(bitwuzla);
}

// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the bitwuzla binary. bitwuzla supports BV,
// Bool, arrays, FP-native, FP-BV, UF, and BV-quantifiers. It does NOT
// support Int/Real arithmetic or `declare-datatypes` (tuples), so those
// fixtures are intentionally absent.
// ---------------------------------------------------------------------------

#define CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST(NameStr, RunFn)                   \
  TEST_CASE("SMTLIB pipeline: " NameStr " [bitwuzla]",                         \
            "[Bitwuzla][SMTLIB][pipeline]") {                                  \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::bitwuzlaCommand(),    \
                                 "bitwuzla");                                  \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST("public factory works",
                                     runSMTLIBPublicFactory)
CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                                     runSMTLIBDualEmitter)
CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST(
    "getBVInBin handles 128-bit decimal model value", runSMTLIBGetBVInBin128)
CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST("native FP infinity model parses",
                                     runSMTLIBNativeFPInfinity)
CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST("native FP NaN model parses",
                                     runSMTLIBNativeFPNaNModel)
CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST(
    "native FP neg FlipSignBit toggles NaN sign", runSMTLIBNativeFPNegFlipNaN)

#undef CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST

#define CAMADA_BITWUZLA_SMTLIB_SHARED_TEST(NameStr, FixtureCall)               \
  TEST_CASE("SMTLIB pipeline: " NameStr " [bitwuzla]",                         \
            "[Bitwuzla][SMTLIB][pipeline]") {                                  \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::bitwuzlaCommand(),    \
                                 "bitwuzla");                                  \
    camada::SMTSolverRef solver =                                              \
        camada_smtlib_pipeline::makeSMTLIBSolver(Cmd);                         \
    FixtureCall;                                                               \
  }

CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("implies_semantics",
                                   implies_semantics(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("implies_true_implies_false",
                                   implies_true_implies_false(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("bv_lshr_semantics",
                                   bv_lshr_semantics(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("incremental_push_pop",
                                   incremental_push_pop(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                                   symbol_cache_survives_push_pop(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("array", array(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("array_const_store_semantics",
                                   array_const_store_semantics(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("bool_array_const_store_semantics",
                                   bool_array_const_store_semantics(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("quantifier_semantics",
                                   quantifier_semantics(solver))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("fp_equal NativeFP",
                                   fp_equal(solver, camada::FPEncoding::Native))
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("fp_equal BVFP",
                                   fp_equal(solver, camada::FPEncoding::BV))

#undef CAMADA_BITWUZLA_SMTLIB_SHARED_TEST
