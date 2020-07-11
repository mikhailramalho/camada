
#include "simple.test.h"

#include <boolectorsolver.h>
#include <catch2/catch.hpp>

TEST_CASE("Simple Boolector test", "[Boolector]") {
  // Create Boolector Solver
  auto btor = camada::createBoolectorSolver();
  equal_ten(btor);
}

TEST_CASE("Override Boolector Solver", "[Boolector]") {

  class myBtorContext : public camada::BtorContext {
  public:
    explicit myBtorContext() : camada::BtorContext() {}

    void createAndConfig() override {
      Context = boolector_new();
      boolector_set_opt(Context, BTOR_OPT_MODEL_GEN, 1);
      boolector_set_opt(Context, BTOR_OPT_AUTO_CLEANUP, 1);
      boolector_set_opt(Context, BTOR_OPT_INCREMENTAL, 1);
    }
  };

  // Create Boolector Solver
  camada::SMTSolverRef btor =
      std::make_shared<camada::BtorSolver>(std::make_shared<myBtorContext>());

  equal_ten(btor);
}
