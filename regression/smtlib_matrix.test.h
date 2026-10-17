#pragma once

// The (fixture x child-solver) cross product for the SMT-LIB pipeline.
// CAMADA_SMTLIB_MATRIX(Child, Tags, CmdFn) instantiates one TEST_CASE per
// pipe-relevant fixture against that child binary, each on a fresh
// SMTLIBSolver, so every child runs every fixture by default. A child
// leaves a cell only through SMTLIBExclusions below, whose reason string is
// mandatory -- there is no supports() to consult for an external binary, so
// the table carries the whole capability story. Never by omission: a hole
// in the matrix is always explained in the output.
//
// The test names and tags keep the historical spelling
// ("SMTLIB pipeline: <fixture> [<child>]", "[<Backend>][SMTLIB][pipeline]").

#include "matrix.test.h" // camada_matrix::Exclusion
#include "smtlib_pipeline.test.h"
#include "tests.h"

#include <catch2/catch_test_macros.hpp>

namespace camada_smtlib_matrix {

using camada_matrix::Exclusion;

// Keyed by the child name as it appears in the test name, and the fixture
// name as printed. These are facts about the child BINARIES, not about
// camada's backends.
constexpr Exclusion SMTLIBExclusions[] = {
    // --- no Int/Real theory in the child ---
    {"bitwuzla", "int_arithmetic_semantics", "the bitwuzla child is BV-only"},
    {"bitwuzla", "real_arithmetic_semantics", "the bitwuzla child is BV-only"},
    {"bitwuzla", "arith_division_semantics", "the bitwuzla child is BV-only"},
    {"bitwuzla", "arith_model_queries", "the bitwuzla child is BV-only"},
    {"bitwuzla", "arith_conversion_semantics", "the bitwuzla child is BV-only"},
    {"bitwuzla", "int_bv_conversion_semantics",
     "the bitwuzla child is BV-only"},
    {"stp", "int_arithmetic_semantics", "the stp child is QF_AUFBV-only"},
    {"stp", "real_arithmetic_semantics", "the stp child is QF_AUFBV-only"},
    {"stp", "arith_division_semantics", "the stp child is QF_AUFBV-only"},
    {"stp", "arith_model_queries", "the stp child is QF_AUFBV-only"},
    {"stp", "arith_conversion_semantics", "the stp child is QF_AUFBV-only"},
    {"stp", "int_bv_conversion_semantics", "the stp child is QF_AUFBV-only"},

    // --- no quantifiers in the child ---
    {"mathsat", "quantifier_semantics",
     "the mathsat binary does not support (forall ...)/(exists ...) under "
     "any logic"},
    {"yices-smt2", "quantifier_semantics",
     "yices-smt2 has no quantifier support"},
    {"stp", "quantifier_semantics", "the stp child is quantifier-free"},

    // --- no (declare-datatypes ...) in the child; the [Camada] rows cover
    //     tuples there ---
    {"bitwuzla", "tuple_semantics [native]",
     "the bitwuzla child rejects declare-datatypes"},
    {"bitwuzla", "tuple_with_array_field [native]",
     "the bitwuzla child rejects declare-datatypes"},
    {"bitwuzla", "empty_tuple_semantics [native]",
     "the bitwuzla child rejects declare-datatypes"},
    {"mathsat", "tuple_semantics [native]",
     "the mathsat child rejects declare-datatypes"},
    {"mathsat", "tuple_with_array_field [native]",
     "the mathsat child rejects declare-datatypes"},
    {"mathsat", "empty_tuple_semantics [native]",
     "the mathsat child rejects declare-datatypes"},
    {"yices-smt2", "tuple_semantics [native]",
     "the yices-smt2 child rejects declare-datatypes"},
    {"yices-smt2", "tuple_with_array_field [native]",
     "the yices-smt2 child rejects declare-datatypes"},
    {"yices-smt2", "empty_tuple_semantics [native]",
     "the yices-smt2 child rejects declare-datatypes"},
    {"stp", "tuple_semantics [native]",
     "the stp child rejects declare-datatypes"},
    {"stp", "tuple_with_array_field [native]",
     "the stp child rejects declare-datatypes"},
    {"stp", "empty_tuple_semantics [native]",
     "the stp child rejects declare-datatypes"},

    // --- no FP theory in the child (the BVFP row still runs: the BV
    //     encoding puts only bit-vectors on the wire) ---
    {"yices-smt2", "fp_equal NativeFP", "yices-smt2 has no FP theory"},
    {"stp", "fp_equal NativeFP", "the stp child has no FP theory"},

    // --- no ((as const ...)) array literals in the child; measured:
    //     yices-smt2 answers `undefined term: const`, stp a syntax error
    //     on `as`. array_model_values stays on: it builds no const array. ---
    {"yices-smt2", "array",
     "yices-smt2 does not implement ((as const ...)) array literals"},
    {"yices-smt2", "array_const_store_semantics",
     "yices-smt2 does not implement ((as const ...)) array literals"},
    {"yices-smt2", "bool_array_const_store_semantics",
     "yices-smt2 does not implement ((as const ...)) array literals"},
    {"stp", "array",
     "the stp child's parser has no ((as const ...)) array literals"},
    {"stp", "array_const_store_semantics",
     "the stp child's parser has no ((as const ...)) array literals"},
    {"stp", "bool_array_const_store_semantics",
     "the stp child's parser has no ((as const ...)) array literals"},

    // --- other measured child limits ---
    {"mathsat", "bool_array_const_store_semantics",
     "the mathsat child rejects Bool-sorted arrays: (error \"Arrays with "
     "Bool as argument are not supported\")"},
    {"stp", "uf_semantics",
     "the stp child's parser rejects declare-fun with arguments"},
    {"stp", "tuple_with_array_field [Camada]",
     "the stp child cannot answer (get-value) of an array select, so the "
     "array-field model query comes back empty"},

    // --- scoped declarations ---
    {"stp", "symbol_cache_survives_push_pop",
     "the stp child answers `unsupported` to :global-declarations true, so "
     "declarations made inside a (push) scope die with the pop"},
};

inline const char *excluded(const char *Child, const char *Fixture) {
  for (const auto &E : SMTLIBExclusions)
    if (std::strcmp(E.Backend, Child) == 0 &&
        std::strcmp(E.Group, Fixture) == 0)
      return E.Reason;
  return nullptr;
}

} // namespace camada_smtlib_matrix

// A fixture driven through the pipe on a fresh SMTLIBSolver. ChildName is
// the lowercase spelling in the test name; Tags the Catch2 tag string.
#define CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, NameStr, MakeFn, ...)        \
  TEST_CASE("SMTLIB pipeline: " NameStr " [" ChildName "]", Tags) {            \
    if (const char *Why = camada_smtlib_matrix::excluded(ChildName, NameStr))  \
      SKIP(Why);                                                               \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::CmdFn(), ChildName);  \
    camada::SMTSolverRef solver = camada_smtlib_pipeline::MakeFn(Cmd);         \
    __VA_ARGS__;                                                               \
  }

// A pipeline-runner scenario (takes the argv, builds its own solver).
#define CAMADA_SMTLIB_RUNNER_ROW(ChildName, Tags, CmdFn, NameStr, RunFn)       \
  TEST_CASE("SMTLIB pipeline: " NameStr " [" ChildName "]", Tags) {            \
    if (const char *Why = camada_smtlib_matrix::excluded(ChildName, NameStr))  \
      SKIP(Why);                                                               \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::CmdFn(), ChildName);  \
    camada_smtlib_pipeline::RunFn(Cmd);                                        \
  }

// clang-format off
#define CAMADA_SMTLIB_MATRIX(ChildName, Tags, CmdFn)                           \
  CAMADA_SMTLIB_RUNNER_ROW(ChildName, Tags, CmdFn, "public factory works",     \
                           runSMTLIBPublicFactory)                             \
  CAMADA_SMTLIB_RUNNER_ROW(ChildName, Tags, CmdFn,                             \
                           "dual emitter logs to file too",                    \
                           runSMTLIBDualEmitter)                               \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "equal_ten",                       \
                    makeSMTLIBSolver, equal_ten(solver))                       \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "implies_semantics",               \
                    makeSMTLIBSolver, implies_semantics(solver))               \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "implies_true_implies_false",      \
                    makeSMTLIBSolver, implies_true_implies_false(solver))      \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "check_sat_assuming_semantics",    \
                    makeSMTLIBSolver, check_sat_assuming_semantics(solver))    \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "bv_lshr_semantics",               \
                    makeSMTLIBSolver, bv_lshr_semantics(solver))               \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "incremental_push_pop",            \
                    makeSMTLIBSolver, incremental_push_pop(solver))            \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn,                                    \
                    "symbol_cache_survives_push_pop", makeSMTLIBSolver,        \
                    symbol_cache_survives_push_pop(solver))                    \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "array",                           \
                    makeSMTLIBSolver, array(solver))                           \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "array_model_values",              \
                    makeSMTLIBSolver, array_model_values(solver))              \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "array_const_store_semantics",     \
                    makeSMTLIBSolver, array_const_store_semantics(solver))     \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn,                                    \
                    "bool_array_const_store_semantics", makeSMTLIBSolver,      \
                    bool_array_const_store_semantics(solver))                  \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "uf_semantics",                    \
                    makeSMTLIBSolver, uf_semantics(solver))                    \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "quantifier_semantics",            \
                    makeSMTLIBSolver, quantifier_semantics(solver))            \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "int_arithmetic_semantics",        \
                    makeSMTLIBSolver, int_arithmetic_semantics(solver))        \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "real_arithmetic_semantics",       \
                    makeSMTLIBSolver, real_arithmetic_semantics(solver))       \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "arith_division_semantics",        \
                    makeSMTLIBSolver, arith_division_semantics(solver))        \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "arith_model_queries",             \
                    makeSMTLIBSolver, arith_model_queries(solver))             \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "arith_conversion_semantics",      \
                    makeSMTLIBSolver, arith_conversion_semantics(solver))      \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "int_bv_conversion_semantics",     \
                    makeSMTLIBSolver, int_bv_conversion_semantics(solver))     \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "tuple_semantics [native]",        \
                    makeSMTLIBSolver, tuple_semantics(solver))                 \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn,                                    \
                    "tuple_with_array_field [native]", makeSMTLIBSolver,       \
                    tuple_with_array_field(solver))                            \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "empty_tuple_semantics [native]",  \
                    makeSMTLIBSolver, empty_tuple_semantics(solver))           \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "tuple_semantics [Camada]",        \
                    makeSMTLIBSolverCamadaTuples, tuple_semantics(solver))     \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn,                                    \
                    "tuple_with_array_field [Camada]",                         \
                    makeSMTLIBSolverCamadaTuples,                              \
                    tuple_with_array_field(solver))                            \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "empty_tuple_semantics [Camada]",  \
                    makeSMTLIBSolverCamadaTuples, empty_tuple_semantics(solver)) \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "fp_equal NativeFP",               \
                    makeSMTLIBSolver,                                          \
                    fp_equal(solver, camada::FPEncoding::Native))              \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "fp_equal BVFP",                   \
                    makeSMTLIBSolver, fp_equal(solver, camada::FPEncoding::BV)) \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "fxp_rounding_semantics",          \
                    makeSMTLIBSolver, fxp_rounding_semantics(solver))          \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "fxp_model_and_constructs",        \
                    makeSMTLIBSolver, fxp_model_and_constructs(solver))
// clang-format on
