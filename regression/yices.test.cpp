
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
    static void configureQfAbv(ctx_config_t *config) {
      yices_set_config(config, "mode", "push-pop");
      yices_set_config(config, "solver-type", "dpllt");
      yices_set_config(config, "uf-solver", "none");
      yices_set_config(config, "bv-solver", "default");
      yices_set_config(config, "array-solver", "default");
      yices_set_config(config, "arith-solver", "none");
    }

    void create() { recreateContextWithConfig("QF_ABV", configureQfAbv); }
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
// The fp_equal NativeFP fixture is therefore absent.
// ---------------------------------------------------------------------------

#define CAMADA_YICES_SMTLIB_PIPELINE_TEST(NameStr, RunFn)                      \
  TEST_CASE("SMTLIB pipeline: " NameStr " [yices-smt2]",                       \
            "[YICES][SMTLIB][pipeline]") {                                     \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::yicesSmt2Command(),   \
                                 "yices-smt2");                                \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_YICES_SMTLIB_PIPELINE_TEST("public factory works",
                                  runSMTLIBPublicFactory)
CAMADA_YICES_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                                  runSMTLIBDualEmitter)

#undef CAMADA_YICES_SMTLIB_PIPELINE_TEST

// `MakeFn` is the camada_smtlib_pipeline factory used to construct the
// SMTLIBSolver — pass `makeSMTLIBSolver` for the default native-tuple
// configuration, or `makeSMTLIBSolverCamadaTuples` to lower tuples into
// per-field BV/Bool symbols on the wire (required against children that
// reject `(declare-datatypes ...)`).
#define CAMADA_YICES_SMTLIB_SHARED_TEST(NameStr, FixtureCall, MakeFn)          \
  TEST_CASE("SMTLIB pipeline: " NameStr " [yices-smt2]",                       \
            "[YICES][SMTLIB][pipeline]") {                                     \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::yicesSmt2Command(),   \
                                 "yices-smt2");                                \
    camada::SMTSolverRef solver = camada_smtlib_pipeline::MakeFn(Cmd);         \
    FixtureCall;                                                               \
  }

CAMADA_YICES_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("implies_semantics", implies_semantics(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("implies_true_implies_false",
                                implies_true_implies_false(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("bv_lshr_semantics", bv_lshr_semantics(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("incremental_push_pop",
                                incremental_push_pop(solver), makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                                symbol_cache_survives_push_pop(solver),
                                makeSMTLIBSolver)
// Array fixtures absent for yices: they all use `mkArrayConst`, which Camada
// emits as `((as const ...) ...)`. yices-smt2 rejects this syntax outright
// ("undefined term: const"); native yices supports const-arrays via a
// different C-API path, but there's no SMT-LIB-wire equivalent.
CAMADA_YICES_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("int_arithmetic_semantics",
                                int_arithmetic_semantics(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("real_arithmetic_semantics",
                                real_arithmetic_semantics(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("arith_model_queries",
                                arith_model_queries(solver), makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("arith_conversion_semantics",
                                arith_conversion_semantics(solver),
                                makeSMTLIBSolver)
CAMADA_YICES_SMTLIB_SHARED_TEST("fp_equal BVFP",
                                fp_equal(solver, camada::FPEncoding::BV),
                                makeSMTLIBSolver)
// yices rejects (declare-datatypes ...), so tuples here must use the
// Camada lowering (per-field BV/Bool symbols).
CAMADA_YICES_SMTLIB_SHARED_TEST("tuple_semantics [Camada]",
                                tuple_semantics(solver),
                                makeSMTLIBSolverCamadaTuples)
CAMADA_YICES_SMTLIB_SHARED_TEST("empty_tuple_semantics [Camada]",
                                empty_tuple_semantics(solver),
                                makeSMTLIBSolverCamadaTuples)

#undef CAMADA_YICES_SMTLIB_SHARED_TEST
