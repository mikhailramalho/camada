

#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <mathsatsolver.h>

TEST_CASE("Simple MathSAT test", "[MathSAT]") {
  // Create Mathsat Solver
  auto mathsat = camada::createMathSATSolver();
  tests(mathsat);
}

TEST_CASE("UF MathSAT test", "[MathSAT]") {
  auto mathsat = camada::createMathSATSolver();
  uf_semantics(mathsat);
}

TEST_CASE("Unsupported quantifiers MathSAT test", "[MathSAT]") {
  auto mathsat = camada::createMathSATSolver();
  require_abort([&]() {
    auto x = mathsat->mkSymbol("x", mathsat->mkBVSort(4));
    (void)mathsat->mkForall({x}, mathsat->mkEqual(x, x));
  });
}

TEST_CASE("Arith MathSAT test", "[MathSAT]") {
  msat_config Config = msat_create_default_config("QF_UFLIRA");
  msat_set_option(Config, "model_generation", "true");
  camada::SMTSolverRef mathsat =
      std::make_unique<camada::MathSATSolver>(Config);

  int_arithmetic_semantics(mathsat);
  mathsat->reset();
  real_arithmetic_semantics(mathsat);
  mathsat->reset();
  arith_model_queries(mathsat);
  mathsat->reset();
  arith_conversion_semantics(mathsat);
}

TEST_CASE("Override MathSAT Solver", "[MathSAT]") {

  class mySolver : public camada::MathSATSolver {
  public:
    explicit mySolver(const msat_config &Config)
        : camada::MathSATSolver(Config) {}
  };

  msat_config Config = msat_create_default_config("AUFBV");

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

  msat_set_option(Config, "model_generation", "true");

  // Create custom MathSAT Solver
  camada::SMTSolverRef mathsat = std::make_unique<mySolver>(Config);

  tests(mathsat);
}

TEST_CASE("MathSAT reset reuses symbol names across sort changes",
          "[MathSAT]") {
  auto mathsat = camada::createMathSATSolver();

  auto eight = mathsat->mkBVFromDec(8, 8);
  auto x_bv = mathsat->mkSymbol("x", mathsat->mkBVSort(8));
  mathsat->addConstraint(mathsat->mkEqual(x_bv, eight));
  REQUIRE(mathsat->check() == camada::checkResult::SAT);
  auto x_bv_res = mathsat->getBV(x_bv);
  REQUIRE(x_bv_res);
  REQUIRE(x_bv_res.value() == 8);

  mathsat->reset();

  auto x_bool = mathsat->mkSymbol("x", mathsat->mkBoolSort());
  mathsat->addConstraint(x_bool);
  REQUIRE(mathsat->check() == camada::checkResult::SAT);
  auto x_bool_res = mathsat->getBool(x_bool);
  REQUIRE(x_bool_res);
  REQUIRE(x_bool_res.value());
}

TEST_CASE("MathSAT solver recreation reuses symbol names", "[MathSAT]") {
  {
    auto mathsat = camada::createMathSATSolver();
    auto x_bv = mathsat->mkSymbol("x", mathsat->mkBVSort(4));
    mathsat->addConstraint(mathsat->mkEqual(x_bv, mathsat->mkBVFromDec(3, 4)));
    REQUIRE(mathsat->check() == camada::checkResult::SAT);
    auto x_bv_res = mathsat->getBV(x_bv);
    REQUIRE(x_bv_res);
    REQUIRE(x_bv_res.value() == 3);
  }

  {
    auto mathsat = camada::createMathSATSolver();
    auto x_bool = mathsat->mkSymbol("x", mathsat->mkBoolSort());
    mathsat->addConstraint(mathsat->mkNot(x_bool));
    REQUIRE(mathsat->check() == camada::checkResult::SAT);
    auto x_bool_res = mathsat->getBool(x_bool);
    REQUIRE(x_bool_res);
    REQUIRE_FALSE(x_bool_res.value());
  }
}
