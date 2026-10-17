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
// Test names are "SMTLIB pipeline: <fixture> [<child>]", tagged
// "[<Backend>][SMTLIB][pipeline]".

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
    // A row names a group (a set of fixtures sharing the same cause) or one
    // fixture; the matrix rows say which group each fixture belongs to.

    // --- no Int/Real theory in the child ---
    {"bitwuzla", "arith", "the bitwuzla child is BV-only"},
    {"stp", "arith", "the stp child is QF_AUFBV-only"},

    // --- no quantifiers in the child ---
    {"mathsat", "quantifier_semantics",
     "the mathsat binary does not support (forall ...)/(exists ...) under "
     "any logic"},
    {"yices-smt2", "quantifier_semantics",
     "yices-smt2 has no quantifier support"},
    {"stp", "quantifier_semantics", "the stp child is quantifier-free"},

    // --- no (declare-datatypes ...) in the child; the [Camada] rows cover
    //     tuples there ---
    {"bitwuzla", "native-tuples",
     "the bitwuzla child rejects declare-datatypes"},
    {"mathsat", "native-tuples", "the mathsat child rejects declare-datatypes"},
    {"yices-smt2", "native-tuples",
     "the yices-smt2 child rejects declare-datatypes"},
    {"stp", "native-tuples", "the stp child rejects declare-datatypes"},

    // --- no FP theory in the child (the BVFP row still runs: the BV
    //     encoding puts only bit-vectors on the wire) ---
    {"yices-smt2", "fp_equal NativeFP", "yices-smt2 has no FP theory"},
    {"stp", "fp_equal NativeFP", "the stp child has no FP theory"},

    // --- no ((as const ...)) array literals in the child; measured:
    //     yices-smt2 answers `undefined term: const`, stp a syntax error
    //     on `as`. array_model_values stays on: it builds no const array. ---
    {"yices-smt2", "const-arrays",
     "yices-smt2 does not implement ((as const ...)) array literals"},
    {"stp", "const-arrays",
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

// The reason a fixture is excluded for a child: through its group ("" for a
// fixture in none) or by its own name.
inline const char *excludedReason(const char *Child, const char *Group,
                                  const char *Fixture) {
  if (const char *Why = camada_matrix::excluded(SMTLIBExclusions, Child, Group))
    return Why;
  return camada_matrix::excluded(SMTLIBExclusions, Child, Fixture);
}

} // namespace camada_smtlib_matrix

// One pipeline test case. SKIPs for an excluded (child, name) pair and when the
// child's binary is not on disk; otherwise runs Body with `Cmd` in scope.
#define CAMADA_SMTLIB_CASE(ChildName, Tags, CmdFn, Group, NameStr, ...)        \
  TEST_CASE("SMTLIB pipeline: " NameStr " [" ChildName "]", Tags) {            \
    if (const char *Why =                                                      \
            camada_smtlib_matrix::excludedReason(ChildName, Group, NameStr))   \
      SKIP(Why);                                                               \
    CAMADA_SMTLIB_REQUIRE_BINARY(camada_smtlib_pipeline::CmdFn(), ChildName);  \
    __VA_ARGS__                                                                \
  }

// A pipeline scenario that takes the child's argv and builds its own solver.
#define CAMADA_SMTLIB_RUNNER_ROW(ChildName, Tags, CmdFn, NameStr, RunFn)       \
  CAMADA_SMTLIB_CASE(ChildName, Tags, CmdFn, "", NameStr,                      \
                     camada_smtlib_pipeline::RunFn(Cmd);)

// A shared fixture on a fresh SMTLIBSolver made by MakeFn, under NameStr, in
// exclusion group Group ("" for none).
#define CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, Group, NameStr, MakeFn, ...) \
  CAMADA_SMTLIB_CASE(ChildName, Tags, CmdFn, Group, NameStr,                   \
                     camada::SMTSolverRef solver =                             \
                         camada_smtlib_pipeline::MakeFn(Cmd);                  \
                     __VA_ARGS__;)

// The common case: named after the fixture, on the default solver.
#define CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, Group, Fixture)          \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, Group, #Fixture, makeSMTLIBSolver, \
                    Fixture(solver))

// clang-format off
#define CAMADA_SMTLIB_MATRIX(ChildName, Tags, CmdFn)                           \
  CAMADA_SMTLIB_RUNNER_ROW(ChildName, Tags, CmdFn, "public factory works",     \
                           runSMTLIBPublicFactory)                             \
  CAMADA_SMTLIB_RUNNER_ROW(ChildName, Tags, CmdFn,                             \
                           "dual emitter logs to file too",                    \
                           runSMTLIBDualEmitter)                               \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", equal_ten)                 \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", implies_semantics)         \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "",                            \
      implies_true_implies_false)                                              \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "",                            \
      check_sat_assuming_semantics)                                            \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", bv_lshr_semantics)         \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", incremental_push_pop)      \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "",                            \
      symbol_cache_survives_push_pop)                                          \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "const-arrays", array)         \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", array_model_values)        \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "const-arrays",                \
      array_const_store_semantics)                                             \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "const-arrays",                \
      bool_array_const_store_semantics)                                        \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", uf_semantics)              \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", quantifier_semantics)      \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "arith",                       \
      int_arithmetic_semantics)                                                \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "arith",                       \
      real_arithmetic_semantics)                                               \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "arith",                       \
      arith_division_semantics)                                                \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "arith", arith_model_queries)  \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "arith",                       \
      arith_conversion_semantics)                                              \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "arith",                       \
      int_bv_conversion_semantics)                                             \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "native-tuples",                   \
      "tuple_semantics [native]", makeSMTLIBSolver, tuple_semantics(solver))   \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "native-tuples",                   \
      "tuple_with_array_field [native]", makeSMTLIBSolver,                     \
      tuple_with_array_field(solver))                                          \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "native-tuples",                   \
      "empty_tuple_semantics [native]", makeSMTLIBSolver,                      \
      empty_tuple_semantics(solver))                                           \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "", "tuple_semantics [Camada]",    \
      makeSMTLIBSolverCamadaTuples, tuple_semantics(solver))                   \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "",                                \
      "tuple_with_array_field [Camada]", makeSMTLIBSolverCamadaTuples,         \
      tuple_with_array_field(solver))                                          \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "",                                \
      "empty_tuple_semantics [Camada]", makeSMTLIBSolverCamadaTuples,          \
      empty_tuple_semantics(solver))                                           \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "", "fp_equal NativeFP",           \
      makeSMTLIBSolver, fp_equal(solver, camada::FPEncoding::Native))          \
  CAMADA_SMTLIB_ROW(ChildName, Tags, CmdFn, "", "fp_equal BVFP",               \
      makeSMTLIBSolver, fp_equal(solver, camada::FPEncoding::BV))              \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", fxp_rounding_semantics)    \
  CAMADA_SMTLIB_FIXTURE(ChildName, Tags, CmdFn, "", fxp_model_and_constructs)
// clang-format on
