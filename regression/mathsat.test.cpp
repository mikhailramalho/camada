

#if SOLVER_SMTLIB_ENABLED
#include "smtlib_pipeline.test.h"
#endif
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

#if SOLVER_SMTLIB_ENABLED
// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the mathsat binary. mathsat supports BV,
// Bool, arrays, FP-native, FP-BV, Int, Real, and UF. It does NOT support
// (forall ...)/(exists ...) under any logic, nor `declare-datatypes`.
// ---------------------------------------------------------------------------

#define CAMADA_MATHSAT_SMTLIB_PIPELINE_TEST(NameStr, RunFn)                    \
  TEST_CASE("SMTLIB pipeline: " NameStr " [mathsat]",                          \
            "[MathSAT][SMTLIB][pipeline]") {                                   \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::mathsatCommand(),     \
                                 "mathsat");                                   \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_MATHSAT_SMTLIB_PIPELINE_TEST("public factory works",
                                    runSMTLIBPublicFactory)
CAMADA_MATHSAT_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                                    runSMTLIBDualEmitter)

#undef CAMADA_MATHSAT_SMTLIB_PIPELINE_TEST

// `MakeFn` is the camada_smtlib_pipeline factory used to construct the
// SMTLIBSolver — pass `makeSMTLIBSolver` for the default native-tuple
// configuration, or `makeSMTLIBSolverCamadaTuples` to lower tuples into
// per-field BV/Bool symbols on the wire (required against children that
// reject `(declare-datatypes ...)`).
#define CAMADA_MATHSAT_SMTLIB_SHARED_TEST(NameStr, FixtureCall, MakeFn)        \
  TEST_CASE("SMTLIB pipeline: " NameStr " [mathsat]",                          \
            "[MathSAT][SMTLIB][pipeline]") {                                   \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::mathsatCommand(),     \
                                 "mathsat");                                   \
    camada::SMTSolverRef solver = camada_smtlib_pipeline::MakeFn(Cmd);         \
    FixtureCall;                                                               \
  }

CAMADA_MATHSAT_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("implies_semantics",
                                  implies_semantics(solver), makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("implies_true_implies_false",
                                  implies_true_implies_false(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("check_sat_assuming_semantics",
                                  check_sat_assuming_semantics(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("bv_lshr_semantics",
                                  bv_lshr_semantics(solver), makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("incremental_push_pop",
                                  incremental_push_pop(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                                  symbol_cache_survives_push_pop(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("array", array(solver), makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("array_model_values",
                                  array_model_values(solver), makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("array_const_store_semantics",
                                  array_const_store_semantics(solver),
                                  makeSMTLIBSolver)
// bool_array_const_store_semantics is absent: mathsat rejects arrays whose
// element sort is Bool ("Arrays with Bool as argument are not supported").
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("int_arithmetic_semantics",
                                  int_arithmetic_semantics(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("real_arithmetic_semantics",
                                  real_arithmetic_semantics(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("arith_model_queries",
                                  arith_model_queries(solver), makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("arith_conversion_semantics",
                                  arith_conversion_semantics(solver),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("fp_equal NativeFP",
                                  fp_equal(solver, camada::FPEncoding::Native),
                                  makeSMTLIBSolver)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("fp_equal BVFP",
                                  fp_equal(solver, camada::FPEncoding::BV),
                                  makeSMTLIBSolver)
// mathsat's SMT-LIB parser rejects (declare-datatypes ...), so tuples here
// must use the Camada lowering (per-field BV/Bool symbols).
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("tuple_semantics [Camada]",
                                  tuple_semantics(solver),
                                  makeSMTLIBSolverCamadaTuples)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("tuple_with_array_field [Camada]",
                                  tuple_with_array_field(solver),
                                  makeSMTLIBSolverCamadaTuples)
CAMADA_MATHSAT_SMTLIB_SHARED_TEST("empty_tuple_semantics [Camada]",
                                  empty_tuple_semantics(solver),
                                  makeSMTLIBSolverCamadaTuples)

#undef CAMADA_MATHSAT_SMTLIB_SHARED_TEST
#endif // SOLVER_SMTLIB_ENABLED

TEST_CASE("MathSAT feature capabilities", "[MathSAT]") {
  auto solver = camada::createMathSATSolver();
  using camada::SolverFeature;
  REQUIRE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE_FALSE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE(solver->supports(SolverFeature::ArrayModels));
}
