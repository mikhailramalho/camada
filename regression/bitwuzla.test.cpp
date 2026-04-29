
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
// scenarios are intentionally absent.
// ---------------------------------------------------------------------------

#define CAMADA_BITWUZLA_SMTLIB_TEST(NameStr, RunFn)                            \
  TEST_CASE("SMTLIB pipeline: " NameStr " [bitwuzla]",                         \
            "[Bitwuzla][SMTLIB][pipeline]") {                                  \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::bitwuzlaCommand(),    \
                                 "bitwuzla");                                  \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_BITWUZLA_SMTLIB_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_BITWUZLA_SMTLIB_TEST("dual emitter logs to file too",
                            runSMTLIBDualEmitter)
CAMADA_BITWUZLA_SMTLIB_TEST("SAT problem returns SAT from check()",
                            runSMTLIBSatProblem)
CAMADA_BITWUZLA_SMTLIB_TEST("UNSAT problem returns UNSAT from check()",
                            runSMTLIBUnsatProblem)
CAMADA_BITWUZLA_SMTLIB_TEST("getBV round-trips a concrete value",
                            runSMTLIBGetBV)
CAMADA_BITWUZLA_SMTLIB_TEST("getBV round-trips a 1-bit value",
                            runSMTLIBGetBV1Bit)
CAMADA_BITWUZLA_SMTLIB_TEST("push/pop returns sat/unsat/sat", runSMTLIBPushPop)
CAMADA_BITWUZLA_SMTLIB_TEST("symbol declared in pushed scope survives pop",
                            runSMTLIBSymbolSurvivesPop)
CAMADA_BITWUZLA_SMTLIB_TEST("getBVInBin handles 128-bit decimal model value",
                            runSMTLIBGetBVInBin128)
CAMADA_BITWUZLA_SMTLIB_TEST("getFP32 round-trips (BV-encoded)",
                            runSMTLIBGetFP32BVEncoded)
CAMADA_BITWUZLA_SMTLIB_TEST("getFP64 round-trips (BV-encoded)",
                            runSMTLIBGetFP64BVEncoded)
CAMADA_BITWUZLA_SMTLIB_TEST("getFP32 round-trips (native FP)",
                            runSMTLIBGetFP32Native)
CAMADA_BITWUZLA_SMTLIB_TEST("getFP64 round-trips (native FP)",
                            runSMTLIBGetFP64Native)
CAMADA_BITWUZLA_SMTLIB_TEST("native FP arithmetic via fp.add",
                            runSMTLIBNativeFPAdd)
CAMADA_BITWUZLA_SMTLIB_TEST("native FP infinity model parses",
                            runSMTLIBNativeFPInfinity)
CAMADA_BITWUZLA_SMTLIB_TEST("native FP neg FlipSignBit toggles NaN sign",
                            runSMTLIBNativeFPNegFlipNaN)
CAMADA_BITWUZLA_SMTLIB_TEST("native FP NaN model parses",
                            runSMTLIBNativeFPNaNModel)
CAMADA_BITWUZLA_SMTLIB_TEST("getArrayElement returns the stored value",
                            runSMTLIBGetArrayElement)
CAMADA_BITWUZLA_SMTLIB_TEST("UF with BV domain/codomain", runSMTLIBUF)
CAMADA_BITWUZLA_SMTLIB_TEST("forall quantifier over BV", runSMTLIBForall)
CAMADA_BITWUZLA_SMTLIB_TEST("exists quantifier finds witness", runSMTLIBExists)

#undef CAMADA_BITWUZLA_SMTLIB_TEST
