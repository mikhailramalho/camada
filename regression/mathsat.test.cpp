
#include "tests.h"
#include "matrix.test.h"

// One test case per shared fixture group; capability gates and
// exclusions live in matrix.test.h.
CAMADA_SHARED_MATRIX(MathSAT, camada::createMathSATSolver)

#include <catch2/catch_test_macros.hpp>
#include <solvers/mathsatsolver.h>

// SolverConfig::Logic drives the MathSAT default-configuration logic.
// Smoke test only: MathSAT's default configuration differs by logic in
// preprocessing/theory tuning, not in which terms a context accepts, so
// there is no deterministic observable that distinguishes QF_BV from the
// default AUFBV here — this pins construction and solving, not the
// specific logic string.
TEST_CASE("Config logic MathSAT test", "[MathSAT]") {
  camada::SolverConfig Cfg;
  Cfg.Logic = "QF_BV";
  auto mathsat = camada::createMathSATSolver(Cfg);
  auto x = mathsat->mkSymbol("x", mathsat->mkBVSort(8));
  mathsat->addConstraint(mathsat->mkEqual(x, mathsat->mkBVFromDec(7, 8)));
  REQUIRE(mathsat->check() == camada::CheckResult::SAT);
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
  REQUIRE(mathsat->check() == camada::CheckResult::SAT);
  auto x_bv_res = mathsat->getBV(x_bv);
  REQUIRE(x_bv_res);
  REQUIRE(x_bv_res.value() == 8);

  mathsat->reset();

  auto x_bool = mathsat->mkSymbol("x", mathsat->mkBoolSort());
  mathsat->addConstraint(x_bool);
  REQUIRE(mathsat->check() == camada::CheckResult::SAT);
  auto x_bool_res = mathsat->getBool(x_bool);
  REQUIRE(x_bool_res);
  REQUIRE(x_bool_res.value());
}

TEST_CASE("MathSAT solver recreation reuses symbol names", "[MathSAT]") {
  {
    auto mathsat = camada::createMathSATSolver();
    auto x_bv = mathsat->mkSymbol("x", mathsat->mkBVSort(4));
    mathsat->addConstraint(mathsat->mkEqual(x_bv, mathsat->mkBVFromDec(3, 4)));
    REQUIRE(mathsat->check() == camada::CheckResult::SAT);
    auto x_bv_res = mathsat->getBV(x_bv);
    REQUIRE(x_bv_res);
    REQUIRE(x_bv_res.value() == 3);
  }

  {
    auto mathsat = camada::createMathSATSolver();
    auto x_bool = mathsat->mkSymbol("x", mathsat->mkBoolSort());
    mathsat->addConstraint(mathsat->mkNot(x_bool));
    REQUIRE(mathsat->check() == camada::CheckResult::SAT);
    auto x_bool_res = mathsat->getBool(x_bool);
    REQUIRE(x_bool_res);
    REQUIRE_FALSE(x_bool_res.value());
  }
}

TEST_CASE("MathSAT feature capabilities", "[MathSAT]") {
  auto solver = camada::createMathSATSolver();
  using camada::SolverFeature;
  REQUIRE(solver->getSolverKind() == camada::SolverKind::MathSAT);
  REQUIRE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE_FALSE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  // Native FP without a native round-to-away term: mkRM aborts for that
  // mode, so callers need the separate bit to know before they build it.
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeRoundToAway));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE(solver->supports(SolverFeature::ArrayModels));
}
