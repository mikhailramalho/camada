
#include "smtlib_pipeline.test.h"
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

TEST_CASE("Tuple Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  tuple_semantics(z3);
}

TEST_CASE("Empty tuple Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  empty_tuple_semantics(z3);
}

TEST_CASE("Override Z3 Solver", "[Z3]") {

  class myZ3Solver : public camada::Z3Solver {
  public:
    explicit myZ3Solver(z3::context C) : camada::Z3Solver(std::move(C)) {
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
  camada::SMTSolverRef z3 = std::make_unique<myZ3Solver>(z3::context{});

  tests(z3);
}

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

CAMADA_Z3_SMTLIB_PIPELINE_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_Z3_SMTLIB_PIPELINE_TEST("dual emitter logs to file too",
                               runSMTLIBDualEmitter)
CAMADA_Z3_SMTLIB_PIPELINE_TEST("getBVInBin handles 128-bit decimal model value",
                               runSMTLIBGetBVInBin128)
CAMADA_Z3_SMTLIB_PIPELINE_TEST("native FP infinity model parses",
                               runSMTLIBNativeFPInfinity)
CAMADA_Z3_SMTLIB_PIPELINE_TEST("native FP NaN model parses",
                               runSMTLIBNativeFPNaNModel)
CAMADA_Z3_SMTLIB_PIPELINE_TEST("native FP neg FlipSignBit toggles NaN sign",
                               runSMTLIBNativeFPNegFlipNaN)

#undef CAMADA_Z3_SMTLIB_PIPELINE_TEST

// Shared fixtures driven through the pipe. Each TEST_CASE creates a fresh
// SMTLIBSolver wrapping the z3 binary and hands it to a fixture from the
// existing native suite. z3 supports the full Camada surface, so we wire up
// one TEST_CASE per fixture that's relevant to a pipe-driven session.
#define CAMADA_Z3_SMTLIB_SHARED_TEST(NameStr, FixtureCall)                     \
  TEST_CASE("SMTLIB pipeline: " NameStr " [z3]", "[Z3][SMTLIB][pipeline]") {   \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::z3Command(), "z3");   \
    camada::SMTSolverRef solver =                                              \
        camada_smtlib_pipeline::makeSMTLIBSolver(Cmd);                         \
    FixtureCall;                                                               \
  }

CAMADA_Z3_SMTLIB_SHARED_TEST("equal_ten", equal_ten(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("implies_semantics", implies_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("implies_true_implies_false",
                             implies_true_implies_false(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("bv_lshr_semantics", bv_lshr_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("incremental_push_pop",
                             incremental_push_pop(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("symbol_cache_survives_push_pop",
                             symbol_cache_survives_push_pop(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("array", array(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("array_const_store_semantics",
                             array_const_store_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("bool_array_const_store_semantics",
                             bool_array_const_store_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("uf_semantics", uf_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("quantifier_semantics",
                             quantifier_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("int_arithmetic_semantics",
                             int_arithmetic_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("real_arithmetic_semantics",
                             real_arithmetic_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("arith_model_queries", arith_model_queries(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("arith_conversion_semantics",
                             arith_conversion_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("tuple_semantics", tuple_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("empty_tuple_semantics",
                             empty_tuple_semantics(solver))
CAMADA_Z3_SMTLIB_SHARED_TEST("fp_equal NativeFP",
                             fp_equal(solver, camada::FPEncoding::Native))
CAMADA_Z3_SMTLIB_SHARED_TEST("fp_equal BVFP",
                             fp_equal(solver, camada::FPEncoding::BV))

#undef CAMADA_Z3_SMTLIB_SHARED_TEST
