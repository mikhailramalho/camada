
#include "smtlib_pipeline.test.h"
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <cvc5solver.h>

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
  arith_symbolic_shift_semantics(cvc5);
}

TEST_CASE("Tuple CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  tuple_semantics(cvc5);
}

TEST_CASE("Empty tuple CVC5 test", "[CVC5]") {
  auto cvc5 = camada::createCVC5Solver();
  empty_tuple_semantics(cvc5);
}

// ---------------------------------------------------------------------------
// SMT-LIB pipeline tests against the cvc5 binary. cvc5 supports the full
// Camada surface (BV, Bool, arrays, FP-native, FP-BV, Int, Real, UF,
// quantifiers, tuples).
// ---------------------------------------------------------------------------

#define CAMADA_CVC5_SMTLIB_TEST(NameStr, RunFn)                                \
  TEST_CASE("SMTLIB pipeline: " NameStr " [cvc5]",                             \
            "[CVC5][SMTLIB][pipeline]") {                                      \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::cvc5Command(),        \
                                 "cvc5");                                      \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

CAMADA_CVC5_SMTLIB_TEST("public factory works", runSMTLIBPublicFactory)
CAMADA_CVC5_SMTLIB_TEST("dual emitter logs to file too", runSMTLIBDualEmitter)
CAMADA_CVC5_SMTLIB_TEST("SAT problem returns SAT from check()",
                        runSMTLIBSatProblem)
CAMADA_CVC5_SMTLIB_TEST("UNSAT problem returns UNSAT from check()",
                        runSMTLIBUnsatProblem)
CAMADA_CVC5_SMTLIB_TEST("getBV round-trips a concrete value", runSMTLIBGetBV)
CAMADA_CVC5_SMTLIB_TEST("getBV round-trips a 1-bit value", runSMTLIBGetBV1Bit)
CAMADA_CVC5_SMTLIB_TEST("push/pop returns sat/unsat/sat", runSMTLIBPushPop)
CAMADA_CVC5_SMTLIB_TEST("symbol declared in pushed scope survives pop",
                        runSMTLIBSymbolSurvivesPop)
CAMADA_CVC5_SMTLIB_TEST("getBVInBin handles 128-bit decimal model value",
                        runSMTLIBGetBVInBin128)
CAMADA_CVC5_SMTLIB_TEST("getFP32 round-trips (BV-encoded)",
                        runSMTLIBGetFP32BVEncoded)
CAMADA_CVC5_SMTLIB_TEST("getFP64 round-trips (BV-encoded)",
                        runSMTLIBGetFP64BVEncoded)
CAMADA_CVC5_SMTLIB_TEST("getFP32 round-trips (native FP)",
                        runSMTLIBGetFP32Native)
CAMADA_CVC5_SMTLIB_TEST("getFP64 round-trips (native FP)",
                        runSMTLIBGetFP64Native)
CAMADA_CVC5_SMTLIB_TEST("native FP arithmetic via fp.add", runSMTLIBNativeFPAdd)
CAMADA_CVC5_SMTLIB_TEST("native FP infinity model parses",
                        runSMTLIBNativeFPInfinity)
CAMADA_CVC5_SMTLIB_TEST("native FP neg FlipSignBit toggles NaN sign",
                        runSMTLIBNativeFPNegFlipNaN)
CAMADA_CVC5_SMTLIB_TEST("native FP NaN model parses", runSMTLIBNativeFPNaNModel)
CAMADA_CVC5_SMTLIB_TEST("getArrayElement returns the stored value",
                        runSMTLIBGetArrayElement)
CAMADA_CVC5_SMTLIB_TEST("getInt round-trips a positive integer",
                        runSMTLIBGetIntPositive)
CAMADA_CVC5_SMTLIB_TEST("getInt round-trips a negative integer",
                        runSMTLIBGetIntNegative)
CAMADA_CVC5_SMTLIB_TEST("integer arithmetic add and compare",
                        runSMTLIBIntArithCompare)
CAMADA_CVC5_SMTLIB_TEST("getRational returns fraction parts (positive)",
                        runSMTLIBGetRationalPositive)
CAMADA_CVC5_SMTLIB_TEST("getRational handles negative rational",
                        runSMTLIBGetRationalNegative)
CAMADA_CVC5_SMTLIB_TEST("int/real conversion and isInt",
                        runSMTLIBIntRealConvIsInt)
CAMADA_CVC5_SMTLIB_TEST("UF with BV domain/codomain", runSMTLIBUF)
CAMADA_CVC5_SMTLIB_TEST("forall quantifier over BV", runSMTLIBForall)
CAMADA_CVC5_SMTLIB_TEST("exists quantifier finds witness", runSMTLIBExists)
CAMADA_CVC5_SMTLIB_TEST("tuple round-trips through projections",
                        runSMTLIBTupleProjection)
CAMADA_CVC5_SMTLIB_TEST("empty tuple is constructible", runSMTLIBEmptyTuple)

#undef CAMADA_CVC5_SMTLIB_TEST
