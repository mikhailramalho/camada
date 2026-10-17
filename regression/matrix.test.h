// The backend x group cross product. CAMADA_SHARED_MATRIX(Backend, Factory)
// in each <backend>.test.cpp instantiates one TEST_CASE per shared fixture
// group, so every backend runs every group by default and each cell is its
// own ctest unit. A backend leaves a cell only through:
//
//   - a capability gate: supports() says the feature is absent, the case
//     SKIPs, and the backend file pins the rejection with its own
//     "Unsupported ..." case; or
//   - an entry in MatrixExclusions below, whose reason string is mandatory.
//
// Never by omission: a hole in the matrix is always explained in the output,
// and every exclusion reason is the record a future "can we re-enable
// this?" starts from.

#pragma once

#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <cstring>

namespace camada_matrix {

struct Exclusion {
  const char *Backend; // the tag spelling, e.g. "Z3"
  const char *Group;
  const char *Reason;
};

// Opt-outs for anything supports() cannot express: upstream bugs, or theory
// limits that have no SolverFeature.
constexpr Exclusion MatrixExclusions[] = {
    {"STP", "nesting",
     "STP's array theory is BV-indexed/BV-valued only, so nested array "
     "sorts abort at construction; the Unsupported nested* STP cases pin "
     "those aborts"},
    {"STP", "nesting-native-const",
     "same as nesting: STP's array theory cannot sort nested arrays"},
    {"Bitwuzla", "nesting-native-const",
     "a native constant array used as an array element always reaches "
     "bitwuzla's array solver, which answers UNKNOWN for CONST_ARRAY "
     "terms; the lazy lowering in the nesting group covers these shapes"},
    {"Yices", "tuple-with-int",
     "the default Yices context enables no arithmetic; Int needs a context "
     "configured for an arithmetic logic (see the Arith Yices test)"},
    {"Yices", "arith",
     "each arith fixture needs a context configured for its logic; the "
     "Arith Yices test runs them on per-logic contexts"},
    {"MathSAT", "arith",
     "the arith fixtures run on a QF_UFLIRA environment in the Arith "
     "MathSAT test (int_bv_conversion on the default one), and "
     "arith_symbolic_shift is wrong there anyway: pow with a symbolic "
     "exponent answers UNSAT on a SAT query, still broken in MathSAT "
     "5.6.19 despite its LA(Z) fixes"},
};

inline const char *excluded(const char *Backend, const char *Group) {
  for (const auto &E : MatrixExclusions)
    if (std::strcmp(E.Backend, Backend) == 0 &&
        std::strcmp(E.Group, Group) == 0)
      return E.Reason;
  return nullptr;
}

} // namespace camada_matrix

#define CAMADA_MATRIX_CASE(Backend, Group, ...)                                \
  TEST_CASE(Group " group " #Backend " test", "[" #Backend "][matrix]") {      \
    if (const char *Why = camada_matrix::excluded(#Backend, Group))            \
      SKIP(Why);                                                               \
    __VA_ARGS__                                                                \
  }

// clang-format off
#define CAMADA_SHARED_MATRIX(Backend, Factory)                                 \
  CAMADA_MATRIX_CASE(Backend, "core", {                                        \
    auto solver = Factory({});                                                 \
    tests_core(solver);                                                        \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "arrays", {                                      \
    auto solver = Factory({});                                                 \
    tests_arrays(solver);                                                      \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "tuples", {                                      \
    auto solver = Factory({});                                                 \
    tests_tuples(solver);                                                      \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "fp", {                                          \
    auto solver = Factory({});                                                 \
    tests_fp(solver);                                                          \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "fxp", {                                         \
    auto solver = Factory({});                                                 \
    tests_fxp(solver);                                                         \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "nesting", {                                     \
    auto solver = Factory({});                                                 \
    tests_nesting(solver);                                                     \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "nesting-native-const", {                        \
    auto solver = Factory({});                                                 \
    tests_nesting_native_const(solver);                                        \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "uf", {                                          \
    auto solver = Factory({});                                                 \
    if (!solver->supports(camada::SolverFeature::UninterpretedFunctions))      \
      SKIP("no UF support; the backend's Unsupported UF case pins the "        \
           "rejection");                                                       \
    uf_semantics(solver);                                                      \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "quantifiers", {                                 \
    auto solver = Factory({});                                                 \
    if (!solver->supports(camada::SolverFeature::Quantifiers))                 \
      SKIP("no quantifier support; the backend's Unsupported quantifiers "     \
           "case pins the rejection");                                         \
    quantifier_semantics(solver);                                              \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "arith", {                                       \
    auto solver = Factory({});                                                 \
    if (!solver->supports(camada::SolverFeature::IntRealArithmetic))           \
      SKIP("no Int/Real arithmetic; the backend's Unsupported arithmetic "     \
           "case pins the rejection");                                         \
    tests_arith(solver);                                                       \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "tuple-with-int", {                              \
    auto solver = Factory({});                                                 \
    if (!solver->supports(camada::SolverFeature::IntRealArithmetic))           \
      SKIP("no Int/Real arithmetic");                                          \
    tuple_semantics_with_int(solver);                                          \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "ackermann-arrays", {                            \
    camada::SolverConfig Cfg;                                                  \
    Cfg.Arrays = camada::ArrayEncoding::Ackermann;                             \
    auto solver = Factory(Cfg);                                                \
    ack_array_tests(solver);                                                   \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "camada-tuples", {                               \
    camada::SolverConfig Cfg;                                                  \
    Cfg.Tuples = camada::TupleEncoding::Camada;                                \
    auto solver = Factory(Cfg);                                                \
    /* supports() reports the backend capability, so a native-datatype */      \
    /* backend still claims it here; tupleMode() is what says this */          \
    /* instance will not use them. Without native datatypes the plain */       \
    /* tuples group already runs the Camada lowering. */                       \
    if (!solver->supports(camada::SolverFeature::NativeTuples))                \
      SKIP("no native datatypes; the tuples group already runs the Camada "    \
           "lowering here");                                                   \
    REQUIRE(solver->tupleMode() == camada::TupleEncoding::Camada);             \
    tuple_semantics(solver);                                                   \
    solver->reset();                                                           \
    tuple_with_array_field(solver);                                            \
    solver->reset();                                                           \
    tuple_array_semantics(solver);                                             \
    solver->reset();                                                           \
    tuple_update_semantics(solver);                                            \
  })                                                                           \
  CAMADA_MATRIX_CASE(Backend, "foreign-handles", {                             \
    auto a = Factory({});                                                      \
    auto b = Factory({});                                                      \
    foreign_handle_rejected(a, b);                                             \
  })
// clang-format on
