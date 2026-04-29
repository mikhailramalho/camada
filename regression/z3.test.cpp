
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
// SMT-LIB pipeline tests against the z3 binary. Each scenario gets its own
// CTest entry so failures and skips report per-test, per-solver.
//
// All scenarios run against z3 — z3 supports the full Camada surface (BV,
// Bool, arrays, FP-native, FP-BV, Int, Real, UF, quantifiers, tuples).
// ---------------------------------------------------------------------------

#define CAMADA_Z3_SMTLIB_TEST(NameStr, RunFn)                                  \
  TEST_CASE("SMTLIB pipeline: " NameStr " [z3]", "[Z3][SMTLIB][pipeline]") {   \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::z3Command(), "z3");   \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_Z3_SMTLIB_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_Z3_SMTLIB_TEST("dual emitter logs to file too", runSMTLIBDualEmitter)
CAMADA_Z3_SMTLIB_TEST("SAT problem returns SAT from check()",
                      runSMTLIBSatProblem)
CAMADA_Z3_SMTLIB_TEST("UNSAT problem returns UNSAT from check()",
                      runSMTLIBUnsatProblem)
CAMADA_Z3_SMTLIB_TEST("getBV round-trips a concrete value", runSMTLIBGetBV)
CAMADA_Z3_SMTLIB_TEST("getBV round-trips a 1-bit value", runSMTLIBGetBV1Bit)
CAMADA_Z3_SMTLIB_TEST("push/pop returns sat/unsat/sat", runSMTLIBPushPop)
CAMADA_Z3_SMTLIB_TEST("symbol declared in pushed scope survives pop",
                      runSMTLIBSymbolSurvivesPop)
CAMADA_Z3_SMTLIB_TEST("getBVInBin handles 128-bit decimal model value",
                      runSMTLIBGetBVInBin128)
CAMADA_Z3_SMTLIB_TEST("getFP32 round-trips (BV-encoded)",
                      runSMTLIBGetFP32BVEncoded)
CAMADA_Z3_SMTLIB_TEST("getFP64 round-trips (BV-encoded)",
                      runSMTLIBGetFP64BVEncoded)
CAMADA_Z3_SMTLIB_TEST("getFP32 round-trips (native FP)", runSMTLIBGetFP32Native)
CAMADA_Z3_SMTLIB_TEST("getFP64 round-trips (native FP)", runSMTLIBGetFP64Native)
CAMADA_Z3_SMTLIB_TEST("native FP arithmetic via fp.add", runSMTLIBNativeFPAdd)
CAMADA_Z3_SMTLIB_TEST("native FP infinity model parses",
                      runSMTLIBNativeFPInfinity)
CAMADA_Z3_SMTLIB_TEST("native FP neg FlipSignBit toggles NaN sign",
                      runSMTLIBNativeFPNegFlipNaN)
CAMADA_Z3_SMTLIB_TEST("native FP NaN model parses", runSMTLIBNativeFPNaNModel)
CAMADA_Z3_SMTLIB_TEST("getArrayElement returns the stored value",
                      runSMTLIBGetArrayElement)
CAMADA_Z3_SMTLIB_TEST("getInt round-trips a positive integer",
                      runSMTLIBGetIntPositive)
CAMADA_Z3_SMTLIB_TEST("getInt round-trips a negative integer",
                      runSMTLIBGetIntNegative)
CAMADA_Z3_SMTLIB_TEST("integer arithmetic add and compare",
                      runSMTLIBIntArithCompare)
CAMADA_Z3_SMTLIB_TEST("getRational returns fraction parts (positive)",
                      runSMTLIBGetRationalPositive)
CAMADA_Z3_SMTLIB_TEST("getRational handles negative rational",
                      runSMTLIBGetRationalNegative)
CAMADA_Z3_SMTLIB_TEST("int/real conversion and isInt",
                      runSMTLIBIntRealConvIsInt)
CAMADA_Z3_SMTLIB_TEST("UF with BV domain/codomain", runSMTLIBUF)
CAMADA_Z3_SMTLIB_TEST("forall quantifier over BV", runSMTLIBForall)
CAMADA_Z3_SMTLIB_TEST("exists quantifier finds witness", runSMTLIBExists)
CAMADA_Z3_SMTLIB_TEST("tuple round-trips through projections",
                      runSMTLIBTupleProjection)
CAMADA_Z3_SMTLIB_TEST("empty tuple is constructible", runSMTLIBEmptyTuple)

#undef CAMADA_Z3_SMTLIB_TEST
