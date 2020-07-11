

#include "simple.test.h"

#include <catch2/catch.hpp>
#include <yicessolver.h>

TEST_CASE("Simple yices test", "[YICES]") {
  // Create Yices Solver
  auto yices = camada::createYicesSolver();
  equal_ten(yices);
}

TEST_CASE("Override Yices Solver", "[YICES]") {

  class myYicesContext : public camada::YicesContext {
  public:
    explicit myYicesContext() : camada::YicesContext() {}

    void createAndConfig() override {
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

      Context = yices_new_context(config);
      yices_free_config(config);
    }
  };

  // Create Yices Solver
  camada::SMTSolverRef yices =
      std::make_shared<camada::YicesSolver>(std::make_shared<myYicesContext>());

  equal_ten(yices);
}
