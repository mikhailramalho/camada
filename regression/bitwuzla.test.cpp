
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

#undef CAMADA_BITWUZLA_SMTLIB_PIPELINE_TEST

// `MakeFn` is the camada_smtlib_pipeline factory used to construct the
// SMTLIBSolver — pass `makeSMTLIBSolver` for the default native-tuple
// configuration, or `makeSMTLIBSolverCamadaTuples` to lower tuples into
// per-field BV/Bool symbols on the wire (required against children that
// reject `(declare-datatypes ...)`).
#define CAMADA_BITWUZLA_SMTLIB_SHARED_TEST(NameStr, FixtureCall, MakeFn)       \
  TEST_CASE("SMTLIB pipeline: " NameStr " [bitwuzla]",                         \
            "[Bitwuzla][SMTLIB][pipeline]") {                                  \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::bitwuzlaCommand(),    \
                                 "bitwuzla");                                  \
    camada::SMTSolverRef solver = camada_smtlib_pipeline::MakeFn(Cmd);         \
    FixtureCall;                                                               \
  }

CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("implies_semantics",
                                   implies_semantics(solver), makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("implies_true_implies_false",
                                   implies_true_implies_false(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("bv_lshr_semantics",
                                   bv_lshr_semantics(solver), makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("incremental_push_pop",
                                   incremental_push_pop(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                                   symbol_cache_survives_push_pop(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("array", array(solver), makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("array_const_store_semantics",
                                   array_const_store_semantics(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("bool_array_const_store_semantics",
                                   bool_array_const_store_semantics(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("quantifier_semantics",
                                   quantifier_semantics(solver),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("fp_equal NativeFP",
                                   fp_equal(solver, camada::FPEncoding::Native),
                                   makeSMTLIBSolver)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("fp_equal BVFP",
                                   fp_equal(solver, camada::FPEncoding::BV),
                                   makeSMTLIBSolver)
// bitwuzla rejects (declare-datatypes ...), so tuples here must use the
// Camada lowering (per-field BV/Bool symbols).
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("tuple_semantics [Camada]",
                                   tuple_semantics(solver),
                                   makeSMTLIBSolverCamadaTuples)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("tuple_with_array_field [Camada]",
                                   tuple_with_array_field(solver),
                                   makeSMTLIBSolverCamadaTuples)
CAMADA_BITWUZLA_SMTLIB_SHARED_TEST("empty_tuple_semantics [Camada]",
                                   empty_tuple_semantics(solver),
                                   makeSMTLIBSolverCamadaTuples)

#undef CAMADA_BITWUZLA_SMTLIB_SHARED_TEST
