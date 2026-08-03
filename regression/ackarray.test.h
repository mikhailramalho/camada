#ifndef CAMADA_REGRESSION_ACKARRAY_TEST_H_
#define CAMADA_REGRESSION_ACKARRAY_TEST_H_

// Fixtures for the Ackermann array encoding (ArrayEncoding::Ackermann).
// Every fixture expects a solver created WITH the Ackermann mode; each
// one pins down a bug class found in the original prototype (constant-
// index reads bypassing congruence, equality frozen at construction, no
// disequality witness, model poisoning, name aliasing) plus the basic
// select/store/const/ite semantics and model queries.

#include "camada.h"

#include <catch2/catch_test_macros.hpp>

// Prototype bug 1: a select at a BV-constant index and a select at a
// symbolic index equal to it must alias.
inline void ack_read_congruence(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(idxsort, elemsort));
  auto i = solver->mkSymbol("i", idxsort);
  auto c3 = solver->mkBVFromDec(3, 8);

  solver->addConstraint(solver->mkEqual(i, c3));
  solver->addConstraint(solver->mkNot(solver->mkEqual(
      solver->mkArraySelect(a, i), solver->mkArraySelect(a, c3))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// Distinct index terms are free to hold different values — and forced
// together the moment the indexes are equated.
inline void ack_distinct_index_reads(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(idxsort, elemsort));
  auto i = solver->mkSymbol("i", idxsort);
  auto j = solver->mkSymbol("j", idxsort);

  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(a, i), solver->mkBVFromDec(1, 8)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(a, j), solver->mkBVFromDec(2, 8)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  solver->push();
  solver->addConstraint(solver->mkEqual(i, j));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
  solver->pop();
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

// Store/select semantics: a store is visible at its own index and
// transparent at every other.
inline void ack_store_select_semantics(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(idxsort, elemsort));
  auto i = solver->mkSymbol("i", idxsort);
  auto j = solver->mkSymbol("j", idxsort);
  auto v = solver->mkBVFromDec(42, 8);
  auto b = solver->mkArrayStore(a, i, v);

  solver->push();
  solver->addConstraint(
      solver->mkNot(solver->mkEqual(solver->mkArraySelect(b, i), v)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
  solver->pop();

  solver->push();
  solver->addConstraint(solver->mkNot(solver->mkEqual(i, j)));
  solver->addConstraint(solver->mkNot(solver->mkEqual(
      solver->mkArraySelect(b, j), solver->mkArraySelect(a, j))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
  solver->pop();
}

// Prototype bug 2: an equality asserted before any reads exist must
// still constrain reads created afterwards.
inline void ack_equality_before_reads(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto arrsort = solver->mkArraySort(idxsort, elemsort);
  auto a = solver->mkSymbol("a", arrsort);
  auto b = solver->mkSymbol("b", arrsort);

  solver->addConstraint(solver->mkEqual(a, b));
  // Reads arrive only now.
  auto k = solver->mkSymbol("k", idxsort);
  solver->addConstraint(solver->mkNot(solver->mkEqual(
      solver->mkArraySelect(a, k), solver->mkArraySelect(b, k))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// Prototype bug 3: `a != b` with no other constraints must be
// satisfiable — a difference must be exhibitable at some index.
inline void ack_disequality_witness(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto arrsort = solver->mkArraySort(idxsort, elemsort);
  auto a = solver->mkSymbol("a", arrsort);
  auto b = solver->mkSymbol("b", arrsort);

  solver->addConstraint(solver->mkNot(solver->mkEqual(a, b)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

// Prototype bug 7: equality over ite-arrays must decide the condition,
// not compare both branches blindly.
inline void ack_ite_array_semantics(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(idxsort, elemsort));
  auto c = solver->mkSymbol("c", solver->mkBoolSort());
  auto i = solver->mkBVFromDec(7, 8);
  auto one = solver->mkBVFromDec(1, 8);
  auto two = solver->mkBVFromDec(2, 8);
  auto x = solver->mkIte(c, solver->mkArrayStore(a, i, one),
                         solver->mkArrayStore(a, i, two));

  solver->push();
  solver->addConstraint(solver->mkEqual(solver->mkArraySelect(x, i), one));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto cval = solver->getBool(c);
  REQUIRE(cval);
  REQUIRE(cval.value());
  solver->pop();

  solver->addConstraint(solver->mkNot(c));
  solver->addConstraint(solver->mkEqual(solver->mkArraySelect(x, i), one));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// Prototype bug 5: model queries must not poison the assertion set — a
// re-check after getArrayElement calls returns the same verdict.
inline void ack_model_query_stability(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(idxsort, elemsort));
  auto v = solver->mkBVFromDec(9, 8);
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(a, solver->mkBVFromDec(1, 8)), v));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Constrained index: exact value. Unconstrained index: some stable
  // value, the same on a repeated query against the same model.
  auto at1 = solver->getArrayElement(a, solver->mkBVFromDec(1, 8));
  auto at1val = solver->getBVInBin(at1);
  REQUIRE(at1val);
  REQUIRE(at1val.value() == "00001001");
  auto at5a = solver->getArrayElement(a, solver->mkBVFromDec(5, 8));
  auto at5b = solver->getArrayElement(a, solver->mkBVFromDec(5, 8));
  auto at5aval = solver->getBVInBin(at5a);
  auto at5bval = solver->getBVInBin(at5b);
  REQUIRE(at5aval);
  REQUIRE(at5bval);
  REQUIRE(at5aval.value() == at5bval.value());

  REQUIRE(solver->check() == camada::checkResult::SAT);
}

// Prototype bug 6: a user symbol shaped like an internal leaf name must
// not alias a read (internal reads live in the reserved __CAMADA_ name
// space, which mkSymbol rejects for users).
inline void ack_internal_name_no_alias(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(idxsort, elemsort));
  auto user = solver->mkSymbol("a__at__00000011", elemsort);
  auto read = solver->mkArraySelect(a, solver->mkBVFromDec(3, 8));

  solver->addConstraint(solver->mkNot(solver->mkEqual(user, read)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

// Constant arrays: every index reads the initializer; stores layer on
// top; the ConstArrayLowering argument is moot in this mode but must be
// accepted.
inline void ack_const_array_semantics(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto init = solver->mkBVFromDec(5, 8);

  for (auto lowering :
       {camada::ConstArrayLowering::Auto, camada::ConstArrayLowering::Native,
        camada::ConstArrayLowering::Lazy}) {
    solver->push();
    auto arr = solver->mkArrayConst(idxsort, init, lowering);
    auto k = solver->mkSymbol("k", idxsort);
    solver->addConstraint(
        solver->mkNot(solver->mkEqual(solver->mkArraySelect(arr, k), init)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
    solver->pop();
  }

  auto arr = solver->mkArrayConst(idxsort, init);
  auto i = solver->mkBVFromDec(2, 8);
  auto v = solver->mkBVFromDec(7, 8);
  auto b = solver->mkArrayStore(arr, i, v);
  solver->addConstraint(solver->mkNot(solver->mkEqual(
      solver->mkArraySelect(b, solver->mkBVFromDec(4, 8)), init)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// getArrayValues: stored indexes appear with their values; a constant
// root reports its initializer as the base.
inline void ack_array_model_values(const camada::SMTSolverRef &solver) {
  auto idxsort = solver->mkBVSort(8);
  auto elemsort = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(idxsort, elemsort));
  auto i = solver->mkBVFromDec(3, 8);
  auto v = solver->mkBVFromDec(42, 8);
  auto b = solver->mkArrayStore(a, i, v);
  // Anchor one read on the root so it shows up as an entry too.
  auto k = solver->mkBVFromDec(1, 8);
  auto w = solver->mkBVFromDec(9, 8);
  solver->addConstraint(solver->mkEqual(solver->mkArraySelect(a, k), w));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  auto model = solver->getArrayValues(b);
  REQUIRE(model);
  bool sawStore = false, sawRead = false;
  for (const auto &entry : model.value().Entries) {
    auto idxval = solver->getBVInBin(entry.first);
    auto elemval = solver->getBVInBin(entry.second);
    REQUIRE(idxval);
    REQUIRE(elemval);
    if (idxval.value() == "00000011") {
      REQUIRE(elemval.value() == "00101010");
      sawStore = true;
    }
    if (idxval.value() == "00000001") {
      REQUIRE(elemval.value() == "00001001");
      sawRead = true;
    }
  }
  REQUIRE(sawStore);
  REQUIRE(sawRead);
  REQUIRE(!model.value().Base);

  auto constArr = solver->mkArrayConst(idxsort, solver->mkBVFromDec(5, 8));
  auto constModel = solver->getArrayValues(constArr);
  REQUIRE(constModel);
  REQUIRE(constModel.value().Base);
  auto baseval = solver->getBVInBin(constModel.value().Base);
  REQUIRE(baseval);
  REQUIRE(baseval.value() == "00000101");
}

// Everything above, against one solver instance with resets in between —
// the entry point backends instantiate.
inline void ack_array_tests(const camada::SMTSolverRef &solver) {
  ack_read_congruence(solver);
  solver->reset();
  ack_distinct_index_reads(solver);
  solver->reset();
  ack_store_select_semantics(solver);
  solver->reset();
  ack_equality_before_reads(solver);
  solver->reset();
  ack_disequality_witness(solver);
  solver->reset();
  ack_ite_array_semantics(solver);
  solver->reset();
  ack_model_query_stability(solver);
  solver->reset();
  ack_internal_name_no_alias(solver);
  solver->reset();
  ack_const_array_semantics(solver);
  solver->reset();
  ack_array_model_values(solver);
}

#endif
