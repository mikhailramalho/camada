
#include "tests.h"

#include <catch2/catch.hpp>
#include <yicessolver.h>

TEST_CASE("Simple Yices test", "[YICES]") {
  // Create Yices Solver
  auto yices = camada::createYicesSolver();
  tests(yices);
}

TEST_CASE("Override Yices Solver", "[YICES]") {

  class myYicesSolver : public camada::YicesSolver {
  public:
    explicit myYicesSolver() { create(); }

    void resetImpl() override {
      SymbolTable.clear();
      Assertions.clear();

      // Delete
      yices_exit();

      // and recreate
      create();
    }

    void create() {
      yices_init();
      yices_clear_error();

      ctx_config_t *config = yices_new_config();
      yices_default_config_for_logic(config, "QF_BV");
      yices_set_config(config, "mode", "one-shot");
      yices_set_config(config, "solver-type", "dpllt");
      yices_set_config(config, "uf-solver", "none");
      yices_set_config(config, "bv-solver", "default");
      yices_set_config(config, "array-solver", "none");
      yices_set_config(config, "arith-solver", "none");

      Context = std::make_shared<context_t *>(yices_new_context(config));
      yices_free_config(config);
    }
  };

  // Create Yices Solver
  camada::SMTSolverRef yices = std::make_shared<myYicesSolver>();

  tests(yices);
}
