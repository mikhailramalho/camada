

#include "tests.h"

#include <catch2/catch.hpp>
#include <mathsatsolver.h>

TEST_CASE("Simple MathSAT test", "[MathSAT]") {
  // Create Mathsat Solver
  auto mathsat = camada::createMathSATSolver();
  tests(mathsat);
}

TEST_CASE("Override MathSAT Solver", "[MathSAT]") {

  class mySolver : public camada::MathSATSolver {
  public:
    explicit mySolver(const msat_config &Config)
        : camada::MathSATSolver(Config) {}
  };

  msat_config Config = msat_create_config();

  // Enable model finding
  msat_set_option(Config, "model_generation", "true");
  msat_set_option(Config, "preprocessor.toplevel_propagation", "true");
  msat_set_option(Config, "preprocessor.simplification", "1");
  msat_set_option(Config, "dpll.branching_random_frequency", "0.01");
  msat_set_option(Config, "dpll.branching_random_invalidate_phase_cache",
                  "true");
  msat_set_option(Config, "dpll.restart_strategy", "3");
  msat_set_option(Config, "dpll.glucose_var_activity", "true");
  msat_set_option(Config, "dpll.glucose_learnt_minimization", "true");
  msat_set_option(Config, "dpll.preprocessor.mode", "1");
  msat_set_option(Config, "theory.bv.eager", "true");
  msat_set_option(Config, "theory.bv.bit_blast_mode", "2");
  msat_set_option(Config, "theory.bv.delay_propagated_eqs", "true");
  msat_set_option(Config, "theory.la.enabled", "false");
  msat_set_option(Config, "theory.fp.mode", "1");
  msat_set_option(Config, "theory.fp.bit_blast_mode", "2");
  msat_set_option(Config, "theory.fp.bv_combination_enabled", "true");
  msat_set_option(Config, "theory.arr.enable_witness", "true");

  // Create custom MathSAT Solver
  camada::SMTSolverRef mathsat = std::make_shared<mySolver>(Config);
  msat_destroy_config(Config);

  tests(mathsat);
}
