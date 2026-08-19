
#if SOLVER_SMTLIB_ENABLED
#include "smtlib_pipeline.test.h"
#endif
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <solvers/cvc5solver.h>

namespace {
// C++17: no designated initializers, so a tiny builder for the one field
// these tests flip.
inline camada::SolverConfig withUnsatAssumptions() {
  camada::SolverConfig Cfg;
  Cfg.UseUnsatAssumptions = true;
  return Cfg;
}
} // namespace

// SolverConfig::Tuples = Camada forces the per-field lowering even though
// cvc5 has native datatypes.
TEST_CASE("Camada tuples via config CVC5 test", "[CVC5]") {
  camada::SolverConfig Cfg;
  Cfg.Tuples = camada::TupleEncoding::Camada;
  auto cvc5 = camada::createCVC5Solver(Cfg);
  REQUIRE_FALSE(cvc5->supports(camada::SolverFeature::NativeTuples));
  tuple_semantics(cvc5);
  cvc5->reset();
  tuple_with_array_field(cvc5);
  cvc5->reset();
  tuple_array_semantics(cvc5);
  cvc5->reset();
  tuple_update_semantics(cvc5);
}

TEST_CASE("Ackermann arrays CVC5 test", "[CVC5]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto cvc5 = camada::createCVC5Solver(Cfg);
  ack_array_tests(cvc5);
}

TEST_CASE("Simple CVC5 test", "[CVC5]") {
  // Create CVC5 Solver
  auto cvc5 = camada::createCVC5Solver();
  tests(cvc5);
}

TEST_CASE("Quantifiers CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  quantifier_semantics(cvc5);
}

TEST_CASE("UF CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  uf_semantics(cvc5);
}

TEST_CASE("Arith CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  int_arithmetic_semantics(cvc5);
  cvc5->reset();
  real_arithmetic_semantics(cvc5);
  cvc5->reset();
  arith_model_queries(cvc5);
  cvc5->reset();
  arith_conversion_semantics(cvc5);
  cvc5->reset();
  int_bv_conversion_semantics(cvc5);
  cvc5->reset();
  arith_symbolic_shift_semantics(cvc5);
}

TEST_CASE("Tuple-with-Int CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  tuple_semantics_with_int(cvc5);
}

#if SOLVER_SMTLIB_ENABLED
// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the cvc5 binary. cvc5 supports the full
// Camada surface (BV, Bool, arrays, FP-native, FP-BV, Int, Real, UF,
// quantifiers, tuples). Same coverage as the z3 pipeline tests.
// ---------------------------------------------------------------------------

#define CAMADA_CVC5_SMTLIB_PIPELINE_TEST(NameStr, RunFn)                       \
  TEST_CASE("SMTLIB pipeline: " NameStr " [cvc5]",                             \
            "[CVC5][SMTLIB][pipeline]") {                                      \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::cvc5Command(),        \
                                 "cvc5");                                      \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_CVC5_SMTLIB_PIPELINE_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_CVC5_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                                 runSMTLIBDualEmitter)

#undef CAMADA_CVC5_SMTLIB_PIPELINE_TEST

// `MakeFn` is the camada_smtlib_pipeline factory used to construct the
// SMTLIBSolver — pass `makeSMTLIBSolver` for the default native-tuple
// configuration, or `makeSMTLIBSolverCamadaTuples` to lower tuples into
// per-field BV/Bool symbols on the wire.
#define CAMADA_CVC5_SMTLIB_SHARED_TEST(NameStr, FixtureCall, MakeFn)           \
  TEST_CASE("SMTLIB pipeline: " NameStr " [cvc5]",                             \
            "[CVC5][SMTLIB][pipeline]") {                                      \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::cvc5Command(),        \
                                 "cvc5");                                      \
    camada::SMTSolverRef solver = camada_smtlib_pipeline::MakeFn(Cmd);         \
    FixtureCall;                                                               \
  }

CAMADA_CVC5_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("implies_semantics", implies_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("implies_true_implies_false",
                               implies_true_implies_false(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("check_sat_assuming_semantics",
                               check_sat_assuming_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("bv_lshr_semantics", bv_lshr_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("incremental_push_pop",
                               incremental_push_pop(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                               symbol_cache_survives_push_pop(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("array", array(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("array_model_values", array_model_values(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("array_const_store_semantics",
                               array_const_store_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("bool_array_const_store_semantics",
                               bool_array_const_store_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("arith_model_queries",
                               arith_model_queries(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("quantifier_semantics",
                               quantifier_semantics(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("int_arithmetic_semantics",
                               int_arithmetic_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("real_arithmetic_semantics",
                               real_arithmetic_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("arith_conversion_semantics",
                               arith_conversion_semantics(solver),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("tuple_semantics [native]",
                               tuple_semantics(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("tuple_with_array_field [native]",
                               tuple_with_array_field(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("empty_tuple_semantics [native]",
                               empty_tuple_semantics(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("fp_equal NativeFP",
                               fp_equal(solver, camada::FPEncoding::Native),
                               makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("fp_equal BVFP",
                               fp_equal(solver, camada::FPEncoding::BV),
                               makeSMTLIBSolver)
// Camada tuple lowering verified against cvc5 too — confirms the emitted
// script is solvable, not just well-formed.
CAMADA_CVC5_SMTLIB_SHARED_TEST("tuple_semantics [Camada]",
                               tuple_semantics(solver),
                               makeSMTLIBSolverCamadaTuples)
CAMADA_CVC5_SMTLIB_SHARED_TEST("tuple_with_array_field [Camada]",
                               tuple_with_array_field(solver),
                               makeSMTLIBSolverCamadaTuples)
CAMADA_CVC5_SMTLIB_SHARED_TEST("empty_tuple_semantics [Camada]",
                               empty_tuple_semantics(solver),
                               makeSMTLIBSolverCamadaTuples)

CAMADA_CVC5_SMTLIB_SHARED_TEST("int_bv_conversion_semantics",
                               int_bv_conversion_semantics(solver),
                               makeSMTLIBSolver)

CAMADA_CVC5_SMTLIB_SHARED_TEST("fxp_rounding_semantics",
                               fxp_rounding_semantics(solver), makeSMTLIBSolver)
CAMADA_CVC5_SMTLIB_SHARED_TEST("fxp_model_and_constructs",
                               fxp_model_and_constructs(solver),
                               makeSMTLIBSolver)

#undef CAMADA_CVC5_SMTLIB_SHARED_TEST
#endif // SOLVER_SMTLIB_ENABLED

TEST_CASE("CVC5 feature capabilities", "[CVC5]") {
  auto solver = camada::createCVC5Solver();
  using camada::SolverFeature;
  REQUIRE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  // The capability is present either way; core extraction is opt-in at
  // construction because producing unsat assumptions slows every check,
  // so a default context reports the capability but leaves it disabled.
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE_FALSE(solver->produceUnsatAssumptions());
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE(solver->supports(SolverFeature::ArrayModels));

  auto withCores = camada::createCVC5Solver(withUnsatAssumptions());
  REQUIRE(withCores->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(withCores->produceUnsatAssumptions());
}

TEST_CASE("Unsat-assumption opt-in CVC5 test", "[CVC5]") {
  // The default solver runs the shared fixture through its
  // core-unsupported branch (inside tests()); the opted-in solver must
  // produce real cores end to end.
  auto solver = camada::createCVC5Solver(withUnsatAssumptions());
  check_sat_assuming_semantics(solver);
  // The shared fixture tolerates core-less backends, so pin explicitly
  // that this solver actually produces one — and that the opt-in survives
  // reset() (cvc5 keeps its options through resetAssertions()).
  solver->reset();
  REQUIRE(solver->supports(camada::SolverFeature::UnsatAssumptions));
  auto a = solver->mkSymbol("a", solver->mkBoolSort());
  REQUIRE(solver->checkSatAssuming({a, solver->mkNot(a)}) ==
          camada::checkResult::UNSAT);
  auto core = solver->getUnsatAssumptions();
  REQUIRE(core);
  REQUIRE(!core.value().empty());
}

// Registered per backend rather than in tests(): the depth-5 shape
// flattens to nested-array leaves, which STP's array theory lacks.
TEST_CASE("Deep tuple/array nesting CVC5 test", "[CVC5]") {
  auto solver = camada::createCVC5Solver();
  tuple_array_deep_nesting(solver);
}

// Registered per backend: nested constant arrays require native constant
// arrays (lazily lowered constant arrays cannot nest).
TEST_CASE("Nested constant tuple arrays CVC5 test", "[CVC5]") {
  auto solver = camada::createCVC5Solver();
  tuple_array_const_nested(solver);
}

// Registered per backend, not in tests(): array_of(array_of(v)) needs a
// nested array sort, which STP's BV-only array theory lacks.
TEST_CASE("Nested constant arrays CVC5 test", "[CVC5]") {
  auto solver = camada::createCVC5Solver();
  nested_const_array_semantics(solver);
  solver->reset();
  nested_const_array_semantics(solver, camada::ConstArrayLowering::Lazy);
  solver->reset();
  nested_const_array_survives_pop(solver);
  solver->reset();
  nested_const_array_survives_pop(solver, camada::ConstArrayLowering::Lazy);
}
