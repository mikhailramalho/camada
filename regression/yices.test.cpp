
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
