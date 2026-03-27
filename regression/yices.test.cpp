
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

TEST_CASE("Arith Yices test", "[YICES]") {

  class myYicesArithSolver : public camada::YicesSolver {
  public:
    explicit myYicesArithSolver(const char *Logic) : Logic(Logic) {
      destroyAndRecreate();
    }

  private:
    void destroyAndRecreate() {
      OwnedContext.reset();
      Context = nullptr;
      yices_exit();
      yices_init();
      yices_clear_error();

      ctx_config_t *config = yices_new_config();
      yices_default_config_for_logic(config, Logic);
      yices_set_config(config, "mode", "push-pop");

      OwnedContext.reset(yices_new_context(config));
      Context = OwnedContext.get();
      yices_free_config(config);
    }

    const char *Logic;
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
}

TEST_CASE("Override Yices Solver", "[YICES]") {

  class myYicesSolver : public camada::YicesSolver {
  public:
    myYicesSolver() = default;

    void resetImpl() override {
      SymbolTable.clear();
      Assertions.clear();

      OwnedContext.reset();
      Context = nullptr;

      yices_exit();

      create();
    }

    void create() {
      yices_init();
      yices_clear_error();

      ctx_config_t *config = yices_new_config();
      yices_default_config_for_logic(config, "QF_BV");
      yices_set_config(config, "mode", "push-pop");
      yices_set_config(config, "solver-type", "dpllt");
      yices_set_config(config, "uf-solver", "none");
      yices_set_config(config, "bv-solver", "default");
      yices_set_config(config, "array-solver", "none");
      yices_set_config(config, "arith-solver", "none");

      OwnedContext.reset(yices_new_context(config));
      Context = OwnedContext.get();
      yices_free_config(config);
    }
  };

  // Create Yices Solver
  camada::SMTSolverRef yices = std::make_unique<myYicesSolver>();

  tests(yices);
}
