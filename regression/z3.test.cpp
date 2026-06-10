
#if SOLVER_SMTLIB_ENABLED
#include "smtlib_pipeline.test.h"
#endif
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <z3solver.h>

TEST_CASE("Simple Z3 test", "[Z3]") {
  // Create Z3 Solver
  auto z3 = camada::createZ3Solver();
  tests(z3);
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
  arith_model_queries(z3);
  z3->reset();
  arith_conversion_semantics(z3);
  z3->reset();
  arith_symbolic_shift_semantics(z3);
}

TEST_CASE("Tuple-with-Int Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  tuple_semantics_with_int(z3);
}

TEST_CASE("Override Z3 Solver", "[Z3]") {

  class myZ3Solver : public camada::Z3Solver {
  public:
    explicit myZ3Solver(std::unique_ptr<z3::context> C)
        : camada::Z3Solver(std::move(C)) {
      setSolver(makeSolver(context()));
    }

  private:
    static z3::solver makeSolver(z3::context &C) {
      return (z3::tactic(C, "simplify") & z3::tactic(C, "solve-eqs") &
              z3::tactic(C, "simplify") & z3::tactic(C, "smt"))
          .mk_solver();
    }
  };

  // Create Z3 Solver
  camada::SMTSolverRef z3 =
      std::make_unique<myZ3Solver>(std::make_unique<z3::context>());

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

#undef CAMADA_Z3_SMTLIB_SHARED_TEST
#endif // SOLVER_SMTLIB_ENABLED
