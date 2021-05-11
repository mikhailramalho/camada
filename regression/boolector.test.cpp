
#include "tests.h"

#include <boolectorsolver.h>
#include <catch2/catch.hpp>

TEST_CASE("Simple Boolector test", "[Boolector]") {
  // Create Boolector Solver
  auto btor = camada::createBoolectorSolver();
  tests(btor);
  delete btor;
}

TEST_CASE("Override Boolector Solver", "[Boolector]") {

  class myBtorSolver : public camada::BtorSolver {
  public:
    explicit myBtorSolver() {
      Context = boolector_new();
      boolector_set_opt(Context, BTOR_OPT_MODEL_GEN, 1);
      boolector_set_opt(Context, BTOR_OPT_AUTO_CLEANUP, 1);
      boolector_set_opt(Context, BTOR_OPT_INCREMENTAL, 1);
    }

    void resetImpl() override {
      // Delete
      boolector_release_all(Context);
      boolector_delete(Context);

      // Create new
      Context = boolector_new();
      boolector_set_opt(Context, BTOR_OPT_MODEL_GEN, 1);
      boolector_set_opt(Context, BTOR_OPT_AUTO_CLEANUP, 1);
      boolector_set_opt(Context, BTOR_OPT_INCREMENTAL, 1);
    }
  };

  // Create Boolector Solver
  camada::SMTSolverRef btor = new myBtorSolver();
  tests(btor);
  delete btor;
}
