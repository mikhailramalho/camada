
#include "smtlib_pipeline.test.h"
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <yicessolver.h>

TEST_CASE("Simple Yices test", "[YICES]") {
  // Create Yices Solver
  auto yices = camada::createYicesSolver();
  tests(yices);
}

TEST_CASE("UF Yices test", "[YICES]") {
  auto yices = camada::createYicesSolver();
  uf_semantics(yices);
}

TEST_CASE("Unsupported quantifiers Yices test", "[YICES]") {
  auto yices = camada::createYicesSolver();
  require_abort([&]() {
    auto x = yices->mkSymbol("x", yices->mkBVSort(4));
    (void)yices->mkExists({x}, yices->mkEqual(x, x));
  });
}

TEST_CASE("Arith Yices test", "[YICES]") {

  class myYicesArithSolver : public camada::YicesSolver {
  public:
    explicit myYicesArithSolver(const char *Logic) {
      recreateContextWithConfig(Logic, configurePushPop);
    }

  private:
    static void configurePushPop(ctx_config_t *config) {
      yices_set_config(config, "mode", "push-pop");
    }
  };

  {
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFLIA");
    auto int_sort = yices->mkIntSort();
    auto x = yices->mkSymbol("x", int_sort);
    auto one = yices->mkInt(1);
    auto three = yices->mkInt(3);
    auto x_plus_one = yices->mkArithAdd(x, one);

    yices->addConstraint(yices->mkEqual(x_plus_one, three));
    yices->addConstraint(yices->mkArithGt(x, one));
    REQUIRE(yices->check() == camada::checkResult::SAT);
  }

  {
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFLRA");
    auto real_sort = yices->mkRealSort();
    auto r = yices->mkSymbol("r", real_sort);
    auto one = yices->mkReal(1);
    auto three = yices->mkReal(3);
    auto r_plus_one = yices->mkArithAdd(r, one);

    yices->addConstraint(yices->mkEqual(r_plus_one, three));
    yices->addConstraint(yices->mkArithGt(r, one));
    REQUIRE(yices->check() == camada::checkResult::SAT);
  }

  {
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFLRA");
    arith_model_queries(yices);
  }

  {
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFLIRA");
    arith_conversion_semantics(yices);
  }
}

TEST_CASE("Override Yices Solver", "[YICES]") {

  class myYicesSolver : public camada::YicesSolver {
  public:
    myYicesSolver() = default;

    void resetImpl() override {
      Assertions.clear();
      create();
    }

  private:
    static void configureQfBv(ctx_config_t *config) {
      yices_set_config(config, "mode", "push-pop");
      yices_set_config(config, "solver-type", "dpllt");
      yices_set_config(config, "uf-solver", "none");
      yices_set_config(config, "bv-solver", "default");
      yices_set_config(config, "array-solver", "none");
      yices_set_config(config, "arith-solver", "none");
    }

    void create() { recreateContextWithConfig("QF_BV", configureQfBv); }
  };

  // Create Yices Solver
  camada::SMTSolverRef yices = std::make_unique<myYicesSolver>();

  tests(yices);
}

TEST_CASE("Yices multi-instance lifecycle edge case", "[YICES]") {
  auto yices1 = camada::createYicesSolver();
  auto yices2 = camada::createYicesSolver(); // Should not abort or break yices1

  auto x = yices1->mkSymbol("x", yices1->mkBVSort(8));
  yices1->addConstraint(yices1->mkEqual(x, yices1->mkBVFromDec(42, 8)));

  auto y = yices2->mkSymbol("y", yices2->mkBVSort(8));
  yices2->addConstraint(yices2->mkEqual(y, yices2->mkBVFromDec(100, 8)));

  REQUIRE(yices1->check() == camada::checkResult::SAT);
  REQUIRE(yices2->check() == camada::checkResult::SAT);

  yices1->reset();
  REQUIRE(yices2->check() == camada::checkResult::SAT); // Still SAT
}

// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the yices-smt2 binary. yices-smt2 supports
// BV, Bool, arrays, FP-BV (via bit-blast), Int, Real, and UF. It does NOT
// support native FP, quantifiers under logic ALL, or `declare-datatypes`.
// ---------------------------------------------------------------------------

#define CAMADA_YICES_SMTLIB_TEST(NameStr, RunFn)                               \
  TEST_CASE("SMTLIB pipeline: " NameStr " [yices-smt2]",                       \
            "[YICES][SMTLIB][pipeline]") {                                     \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::yicesSmt2Command(),   \
                                 "yices-smt2");                                \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_YICES_SMTLIB_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_YICES_SMTLIB_TEST("dual emitter logs to file too", runSMTLIBDualEmitter)
CAMADA_YICES_SMTLIB_TEST("SAT problem returns SAT from check()",
                         runSMTLIBSatProblem)
CAMADA_YICES_SMTLIB_TEST("UNSAT problem returns UNSAT from check()",
                         runSMTLIBUnsatProblem)
CAMADA_YICES_SMTLIB_TEST("getBV round-trips a concrete value", runSMTLIBGetBV)
CAMADA_YICES_SMTLIB_TEST("getBV round-trips a 1-bit value", runSMTLIBGetBV1Bit)
CAMADA_YICES_SMTLIB_TEST("push/pop returns sat/unsat/sat", runSMTLIBPushPop)
CAMADA_YICES_SMTLIB_TEST("symbol declared in pushed scope survives pop",
                         runSMTLIBSymbolSurvivesPop)
CAMADA_YICES_SMTLIB_TEST("getBVInBin handles 128-bit decimal model value",
                         runSMTLIBGetBVInBin128)
CAMADA_YICES_SMTLIB_TEST("getFP32 round-trips (BV-encoded)",
                         runSMTLIBGetFP32BVEncoded)
CAMADA_YICES_SMTLIB_TEST("getFP64 round-trips (BV-encoded)",
                         runSMTLIBGetFP64BVEncoded)
CAMADA_YICES_SMTLIB_TEST("getArrayElement returns the stored value",
                         runSMTLIBGetArrayElement)
CAMADA_YICES_SMTLIB_TEST("getInt round-trips a positive integer",
                         runSMTLIBGetIntPositive)
CAMADA_YICES_SMTLIB_TEST("getInt round-trips a negative integer",
                         runSMTLIBGetIntNegative)
CAMADA_YICES_SMTLIB_TEST("integer arithmetic add and compare",
                         runSMTLIBIntArithCompare)
CAMADA_YICES_SMTLIB_TEST("getRational returns fraction parts (positive)",
                         runSMTLIBGetRationalPositive)
CAMADA_YICES_SMTLIB_TEST("getRational handles negative rational",
                         runSMTLIBGetRationalNegative)
CAMADA_YICES_SMTLIB_TEST("int/real conversion and isInt",
                         runSMTLIBIntRealConvIsInt)
CAMADA_YICES_SMTLIB_TEST("UF with BV domain/codomain", runSMTLIBUF)

#undef CAMADA_YICES_SMTLIB_TEST
