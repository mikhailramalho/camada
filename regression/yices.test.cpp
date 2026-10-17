#include "matrix.test.h"
#include "tests.h"

// One test case per shared fixture group; capability gates and
// exclusions live in matrix.test.h.
CAMADA_SHARED_MATRIX(Yices, camada::createYicesSolver)

#include <catch2/catch_test_macros.hpp>
#include <solvers/yicessolver.h>

// SolverConfig::Logic drives the Yices context logic; it must survive
// reset(), which recreates the context.
TEST_CASE("Config logic Yices test", "[YICES]") {
  camada::SolverConfig Cfg;
  Cfg.Logic = "QF_BV";
  auto yices = camada::createYicesSolver(Cfg);
  auto x = yices->mkSymbol("x", yices->mkBVSort(8));
  yices->addConstraint(yices->mkEqual(x, yices->mkBVFromDec(7, 8)));
  REQUIRE(yices->check() == camada::CheckResult::SAT);
  yices->reset();
  auto y = yices->mkSymbol("y", yices->mkBVSort(8));
  yices->addConstraint(yices->mkEqual(y, yices->mkBVFromDec(9, 8)));
  REQUIRE(yices->check() == camada::CheckResult::SAT);

  // Pin that the logic actually reached the context: a QF_BV context has
  // no array solver, so asserting an array constraint aborts — under the
  // default QF_AUFBV it would work. Fails if the Logic plumbing is ever
  // dropped.
  require_abort([&]() {
    camada::SolverConfig BVOnly;
    BVOnly.Logic = "QF_BV";
    auto s = camada::createYicesSolver(BVOnly);
    auto bv8 = s->mkBVSort(8);
    auto a = s->mkSymbol("a", s->mkArraySort(bv8, bv8));
    s->addConstraint(s->mkEqual(s->mkArraySelect(a, s->mkBVFromDec(1, 8)),
                                s->mkBVFromDec(2, 8)));
    (void)s->check();
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
    REQUIRE(yices->supports(camada::SolverFeature::IntRealArithmetic));
    auto int_sort = yices->mkIntSort();
    auto x = yices->mkSymbol("x", int_sort);
    auto one = yices->mkInt(1);
    auto three = yices->mkInt(3);
    auto x_plus_one = yices->mkArithAdd(x, one);

    yices->addConstraint(yices->mkEqual(x_plus_one, three));
    yices->addConstraint(yices->mkArithGt(x, one));
    REQUIRE(yices->check() == camada::CheckResult::SAT);
  }

  {
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFLRA");
    REQUIRE(yices->supports(camada::SolverFeature::IntRealArithmetic));
    auto real_sort = yices->mkRealSort();
    auto r = yices->mkSymbol("r", real_sort);
    auto one = yices->mkReal(1);
    auto three = yices->mkReal(3);
    auto r_plus_one = yices->mkArithAdd(r, one);

    yices->addConstraint(yices->mkEqual(r_plus_one, three));
    yices->addConstraint(yices->mkArithGt(r, one));
    REQUIRE(yices->check() == camada::CheckResult::SAT);
  }

  {
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFLRA");
    REQUIRE(yices->supports(camada::SolverFeature::IntRealArithmetic));
    arith_model_queries(yices);
  }

  {
    // The Int<->BV conversions mix theories, which yices only enables
    // through a context configured for a combined logic.
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFBVLIA");
    REQUIRE(yices->supports(camada::SolverFeature::IntRealArithmetic));
    int_bv_conversion_semantics(yices);
  }

  {
    camada::SMTSolverRef yices =
        std::make_unique<myYicesArithSolver>("QF_UFLIRA");
    REQUIRE(yices->supports(camada::SolverFeature::IntRealArithmetic));
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

  REQUIRE(yices1->check() == camada::CheckResult::SAT);
  REQUIRE(yices2->check() == camada::CheckResult::SAT);

  yices1->reset();
  REQUIRE(yices2->check() == camada::CheckResult::SAT); // Still SAT
}

TEST_CASE("Yices feature capabilities", "[Yices]") {
  auto solver = camada::createYicesSolver();
  using camada::SolverFeature;
  REQUIRE(solver->getSolverKind() == camada::SolverKind::Yices);
  // The default QF_AUFBV context has no arithmetic; see the creation-logic
  // test below.
  REQUIRE_FALSE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE_FALSE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
#if defined(_WIN32)
  REQUIRE_FALSE(solver->supports(SolverFeature::Timeouts));
#else
  REQUIRE(solver->supports(SolverFeature::Timeouts));
#endif
  REQUIRE(solver->supports(SolverFeature::ArrayModels));
}

// A Yices context holds only the theories its logic names, so Int/Real support
// is a property of the logic the solver was created with. Each logic below was
// checked against Yices itself: a real inequality asserts under the arithmetic
// ones and is rejected ("the context does not support arithmetic") under the
// others.
TEST_CASE("Yices Int/Real support follows the creation logic", "[YICES]") {
  const auto supportsArith = [](const char *Logic) {
    camada::SolverConfig Cfg;
    Cfg.Logic = Logic;
    return camada::createYicesSolver(Cfg)->supports(
        camada::SolverFeature::IntRealArithmetic);
  };

  REQUIRE_FALSE(camada::createYicesSolver()->supports(
      camada::SolverFeature::IntRealArithmetic));
  for (const char *Logic :
       {"QF_AUFBV", "QF_BV", "QF_UF", "QF_UFBV", "QF_ABV", "QF_AX"}) {
    CAPTURE(Logic);
    REQUIRE_FALSE(supportsArith(Logic));
  }
  for (const char *Logic :
       {"QF_LIA", "QF_LRA", "QF_IDL", "QF_RDL", "QF_UFLIA", "QF_UFLRA",
        "QF_UFLIRA", "QF_UFBVLIA", "QF_AUFLIA", "QF_AUFLIRA", "ALL"}) {
    CAPTURE(Logic);
    REQUIRE(supportsArith(Logic));
  }

  // The capability is the context's, so it survives a reset.
  camada::SolverConfig Cfg;
  Cfg.Logic = "QF_UFLIA";
  auto arith = camada::createYicesSolver(Cfg);
  arith->reset();
  REQUIRE(arith->supports(camada::SolverFeature::IntRealArithmetic));
  (void)arith->mkIntSort();
}

// Without arithmetic in the context, asking for an Int or Real sort is
// rejected where it is made, not at the first arithmetic assertion.
TEST_CASE("Yices rejects Int/Real sorts without an arithmetic logic",
          "[YICES]") {
  auto yices = camada::createYicesSolver();
  require_abort([&]() { (void)yices->mkIntSort(); });
  require_abort([&]() { (void)yices->mkRealSort(); });
}
