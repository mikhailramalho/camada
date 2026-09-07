
#if SOLVER_SMTLIB_ENABLED
#include "smtlib_pipeline.test.h"
#endif
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <solvers/z3solver.h>

TEST_CASE("Simple Z3 test", "[Z3]") {
  // Create Z3 Solver
  auto z3 = camada::createZ3Solver();
  tests(z3);
}

// The fixed<->float oracle tables bit-blast thousands of FP circuits, so
// unlike the other FXP fixtures they run on one backend instead of all
// seven. The conversions are pure common-layer encoding over BV ops that
// every backend already exercises, and the encoding-sensitive cases are
// pinned per backend by fxp_fp_conversion_semantics inside tests().
// Every input of both 16-bit _Accum formats through mkFXPExp. Each exp is
// a wide multiply chain, so this costs ~130s and runs on one backend
// rather than all seven; the encoding is common-layer BV, so the other
// backends' spot checks in tests() are enough.
TEST_CASE("Fixed-point exp exhaustive Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  fxp_exp_exhaustive(z3);
}

TEST_CASE("Fixed-point/floating-point oracle Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  fxp_oracle_fp_semantics(z3, camada::FPEncoding::BV);
}

TEST_CASE("Quantifiers Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  quantifier_semantics(z3);
}

TEST_CASE("UF Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  uf_semantics(z3);
}

TEST_CASE("Arith Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  int_arithmetic_semantics(z3);
  z3->reset();
  real_arithmetic_semantics(z3);
  z3->reset();
  arith_division_semantics(z3);
  z3->reset();
  arith_model_queries(z3);
  z3->reset();
  arith_conversion_semantics(z3);
  z3->reset();
  int_bv_conversion_semantics(z3);
  z3->reset();
  arith_symbolic_shift_semantics(z3);
}

TEST_CASE("Tuple-with-Int Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  tuple_semantics_with_int(z3);
}

// SolverConfig::Tuples = Camada forces the per-field lowering even though
// Z3 has native datatypes — the datatype engine stays out of the picture.
TEST_CASE("Camada tuples via config Z3 test", "[Z3]") {
  camada::SolverConfig Cfg;
  Cfg.Tuples = camada::TupleEncoding::Camada;
  auto z3 = camada::createZ3Solver(Cfg);
  // supports() reports the backend capability, so Z3 still claims native
  // datatypes here; tupleMode() is what says this instance will not use
  // them.
  REQUIRE(z3->supports(camada::SolverFeature::NativeTuples));
  REQUIRE(z3->tupleMode() == camada::TupleEncoding::Camada);
  tuple_semantics(z3);
  z3->reset();
  tuple_with_array_field(z3);
  z3->reset();
  tuple_array_semantics(z3);
  z3->reset();
  tuple_update_semantics(z3);
}

TEST_CASE("Ackermann arrays Z3 test", "[Z3]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto z3 = camada::createZ3Solver(Cfg);
  ack_array_tests(z3);
}

// The full shared fixture suite under the Ackermann encoding — the same
// coverage the native-array mode gets, so every composition (const
// arrays, tuples, FP, FXP, push/pop, models) is proven against the
// encoding, not just the targeted ack_* fixtures.
TEST_CASE("Ackermann full fixture suite Z3 test", "[Z3]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto z3 = camada::createZ3Solver(Cfg);
  tests(z3);
}

TEST_CASE("Ackermann arrays reject quantifiers Z3 test", "[Z3]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto z3 = camada::createZ3Solver(Cfg);
  require_abort([&]() {
    auto x = z3->mkSymbol("x", z3->mkBVSort(4));
    (void)z3->mkForall({x}, z3->mkEqual(x, x));
  });
}

TEST_CASE("Override Z3 Solver", "[Z3]") {

  class myZ3Solver : public camada::Z3Solver {
  public:
    explicit myZ3Solver(z3::config &Cfg) : camada::Z3Solver(Cfg) {
      setSolver(makeSolver(context()));
    }

  private:
    static z3::solver makeSolver(z3::context &C) {
      return (z3::tactic(C, "simplify") & z3::tactic(C, "solve-eqs") &
              z3::tactic(C, "simplify") & z3::tactic(C, "smt"))
          .mk_solver();
    }
  };

  // Create Z3 Solver from a caller-owned configuration; the context is
  // built inside the solver (z3::context cannot be moved in Z3 4.13.x).
  z3::config Cfg;
  camada::SMTSolverRef z3 = std::make_unique<myZ3Solver>(Cfg);

  tests(z3);
}

#if SOLVER_SMTLIB_ENABLED
// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the z3 binary.
//
// Each test wraps the z3 binary in an SMTLIBSolver and drives it through one
// of the existing native fixtures (tests.h / simple.test.h / fp.test.h /
// array.test.h / tuple.test.h) — that's the same coverage the native Z3
// backend gets, just shipped over the SMT-LIB pipe. A handful of pipeline-
// specific scenarios (factory, dual file+pipe emission, the model-value
// shapes only the SMT-LIB pipe surfaces) live in smtlib_pipeline.test.h.
// ---------------------------------------------------------------------------

// Pipeline-specific scenarios.
#define CAMADA_Z3_SMTLIB_PIPELINE_TEST(NameStr, RunFn)                         \
  TEST_CASE("SMTLIB pipeline: " NameStr " [z3]", "[Z3][SMTLIB][pipeline]") {   \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::z3Command(), "z3");   \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

// Pipeline-only scenarios — no native counterpart in tests.h. The
// model-value parsing edge cases (wide BV, FP +oo, FP NaN) and the
// FlipSignBit-on-NaN round-trip are now polymorphic fixtures in
// simple.test.h / fp.test.h and run via tests(solver) below.
CAMADA_Z3_SMTLIB_PIPELINE_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_Z3_SMTLIB_PIPELINE_TEST("factory reports setup failure",
                               runSMTLIBFactoryReportsSetupFailure)
CAMADA_Z3_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                               runSMTLIBDualEmitter)

#undef CAMADA_Z3_SMTLIB_PIPELINE_TEST

// Shared fixtures driven through the pipe. Each TEST_CASE creates a fresh
// SMTLIBSolver wrapping the z3 binary and hands it to a fixture from the
// existing native suite. z3 supports the full Camada surface, so we wire up
// one TEST_CASE per fixture that's relevant to a pipe-driven session.
// `MakeFn` is the camada_smtlib_pipeline factory used to construct the
// SMTLIBSolver — pass `makeSMTLIBSolver` for the default native-tuple
// configuration, or `makeSMTLIBSolverCamadaTuples` to lower tuples into
// per-field BV/Bool symbols on the wire.
#define CAMADA_Z3_SMTLIB_SHARED_TEST(NameStr, FixtureCall, MakeFn)             \
  TEST_CASE("SMTLIB pipeline: " NameStr " [z3]", "[Z3][SMTLIB][pipeline]") {   \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::z3Command(), "z3");   \
    camada::SMTSolverRef solver = camada_smtlib_pipeline::MakeFn(Cmd);         \
    FixtureCall;                                                               \
  }

CAMADA_Z3_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("implies_semantics", implies_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("implies_true_implies_false",
                             implies_true_implies_false(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("check_sat_assuming_semantics",
                             check_sat_assuming_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("bv_lshr_semantics", bv_lshr_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("incremental_push_pop",
                             incremental_push_pop(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                             symbol_cache_survives_push_pop(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("array", array(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("array_model_values", array_model_values(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("array_const_store_semantics",
                             array_const_store_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("bool_array_const_store_semantics",
                             bool_array_const_store_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("quantifier_semantics",
                             quantifier_semantics(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("int_arithmetic_semantics",
                             int_arithmetic_semantics(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("real_arithmetic_semantics",
                             real_arithmetic_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("arith_division_semantics",
                             arith_division_semantics(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("arith_model_queries", arith_model_queries(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("arith_conversion_semantics",
                             arith_conversion_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("tuple_semantics [native]",
                             tuple_semantics(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("tuple_with_array_field [native]",
                             tuple_with_array_field(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("empty_tuple_semantics [native]",
                             empty_tuple_semantics(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("fp_equal NativeFP",
                             fp_equal(solver, camada::FPEncoding::Native),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("fp_equal BVFP",
                             fp_equal(solver, camada::FPEncoding::BV),
                             makeSMTLIBSolver)
// Camada tuple lowering verified against z3 too — confirms the emitted
// script is actually solvable, not just well-formed.
CAMADA_Z3_SMTLIB_SHARED_TEST("tuple_semantics [Camada]",
                             tuple_semantics(solver),
                             makeSMTLIBSolverCamadaTuples)
CAMADA_Z3_SMTLIB_SHARED_TEST("tuple_with_array_field [Camada]",
                             tuple_with_array_field(solver),
                             makeSMTLIBSolverCamadaTuples)
CAMADA_Z3_SMTLIB_SHARED_TEST("empty_tuple_semantics [Camada]",
                             empty_tuple_semantics(solver),
                             makeSMTLIBSolverCamadaTuples)

CAMADA_Z3_SMTLIB_SHARED_TEST("int_bv_conversion_semantics",
                             int_bv_conversion_semantics(solver),
                             makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("fxp_rounding_semantics",
                             fxp_rounding_semantics(solver), makeSMTLIBSolver)
CAMADA_Z3_SMTLIB_SHARED_TEST("fxp_model_and_constructs",
                             fxp_model_and_constructs(solver), makeSMTLIBSolver)

// Ackermann array encoding over the pipe: the wire carries no array
// theory at all — only the read variables and their congruence axioms.
CAMADA_Z3_SMTLIB_SHARED_TEST("ack_array_tests [Ackermann]",
                             ack_array_tests(solver),
                             makeSMTLIBSolverAckermannArrays)

#undef CAMADA_Z3_SMTLIB_SHARED_TEST
#endif // SOLVER_SMTLIB_ENABLED

TEST_CASE("Z3 feature capabilities", "[Z3]") {
  auto solver = camada::createZ3Solver();
  using camada::SolverFeature;
  REQUIRE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE(solver->supports(SolverFeature::NativeRoundToAway));
  REQUIRE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE(solver->supports(SolverFeature::ArrayModels));
}

// Registered per backend rather than in tests(): the depth-5 shape
// flattens to nested-array leaves, which STP's array theory lacks.
TEST_CASE("Deep tuple/array nesting Z3 test", "[Z3]") {
  auto solver = camada::createZ3Solver();
  tuple_array_deep_nesting(solver);
}

// Registered per backend: nested constant arrays require native constant
// arrays (lazily lowered constant arrays cannot nest).
TEST_CASE("Nested constant tuple arrays Z3 test", "[Z3]") {
  auto solver = camada::createZ3Solver();
  tuple_array_const_nested(solver);
}

// Registered per backend, not in tests(): array_of(array_of(v)) needs a
// nested array sort, which STP's BV-only array theory lacks.
TEST_CASE("Nested constant arrays Z3 test", "[Z3]") {
  auto solver = camada::createZ3Solver();
  nested_const_array_semantics(solver);
  solver->reset();
  nested_const_array_semantics(solver, camada::ConstArrayLowering::Lazy);
  solver->reset();
  nested_const_array_survives_pop(solver);
  solver->reset();
  nested_const_array_survives_pop(solver, camada::ConstArrayLowering::Lazy);
}

TEST_CASE("Foreign handle rejection Z3 test", "[Z3]") {
  auto a = camada::createZ3Solver();
  auto b = camada::createZ3Solver();
  foreign_handle_rejected(a, b);
}
