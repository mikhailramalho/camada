
#include "camada.h"

#include <bitset>
#include <catch2/catch_test_macros.hpp>

inline void array(const camada::SMTSolverRef &solver) {
  // An array
  auto indexsort = solver->mkBVSort(2);
  auto elemsort = solver->mkBVSort(10);
  auto init = solver->mkBVFromDec(5, 10);
  REQUIRE(init->getKind() == camada::SMTExprKind::BVConst);
  auto arr = solver->mkArrayConst(indexsort, init);
  REQUIRE(arr->getKind() == camada::SMTExprKind::ArrayConst);

  auto arr1 = solver->mkSymbol("f1", solver->mkArraySort(indexsort, elemsort));
  REQUIRE(arr1->getKind() == camada::SMTExprKind::Symbol);
  auto index = solver->mkBVFromDec(1, 2);
  auto element = solver->mkBVFromDec(10, 10);
  REQUIRE(index->getKind() == camada::SMTExprKind::BVConst);
  REQUIRE(element->getKind() == camada::SMTExprKind::BVConst);
  auto arr11 = solver->mkArrayStore(arr1, index, element);
  REQUIRE(arr11->getKind() == camada::SMTExprKind::ArrayStore);
  auto neq = solver->mkEqual(arr, arr11);
  REQUIRE(neq->getKind() == camada::SMTExprKind::Equal);
  auto eq = solver->mkNot(neq);
  REQUIRE(eq->getKind() == camada::SMTExprKind::Not);

  // Add the constraint to the solver, And check for satisfiability
  solver->addConstraint(eq);
  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto selected = solver->getArrayElement(arr11, solver->mkBVFromDec(1, 2));
  REQUIRE(selected->Sort == elemsort);
  auto selected_res = solver->getBVInBin(selected);
  REQUIRE(selected_res);
  REQUIRE(selected_res.value() == "0000001010");
}

inline void array_const_store_semantics(const camada::SMTSolverRef &solver) {
  auto indexsort = solver->mkBVSort(3);
  auto elemsort = solver->mkBVSort(8);

  auto init = solver->mkBVFromDec(170, elemsort);
  auto stored = solver->mkBVFromDec(17, elemsort);
  auto idx_written = solver->mkBVFromDec(3, indexsort);
  auto idx_other = solver->mkBVFromDec(5, indexsort);

  auto arr = solver->mkArrayConst(indexsort, init);
  auto updated = solver->mkArrayStore(arr, idx_written, stored);

  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_written), stored));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_other), init));

  REQUIRE(solver->check() == camada::checkResult::SAT);

  auto read_written = solver->getArrayElement(updated, idx_written);
  auto read_other = solver->getArrayElement(updated, idx_other);

  REQUIRE(read_written->Sort == elemsort);
  REQUIRE(read_other->Sort == elemsort);
  auto read_written_res = solver->getBVInBin(read_written);
  auto read_other_res = solver->getBVInBin(read_other);
  REQUIRE(read_written_res);
  REQUIRE(read_other_res);
  REQUIRE(read_written_res.value() == "00010001");
  REQUIRE(read_other_res.value() == "10101010");
}

inline void
bool_array_const_store_semantics(const camada::SMTSolverRef &solver) {
  auto indexsort = solver->mkBVSort(2);
  auto boolsort = solver->mkBoolSort();

  auto init = solver->mkBool(false);
  auto stored = solver->mkBool(true);
  auto idx_written = solver->mkBVFromDec(1, indexsort);
  auto idx_other = solver->mkBVFromDec(2, indexsort);

  auto arr = solver->mkArrayConst(indexsort, init);
  REQUIRE(arr->getKind() == camada::SMTExprKind::ArrayConst);
  REQUIRE(arr->Sort->getElementSort() == boolsort);

  auto updated = solver->mkArrayStore(arr, idx_written, stored);
  REQUIRE(updated->getKind() == camada::SMTExprKind::ArrayStore);
  REQUIRE(updated->Sort->getElementSort() == boolsort);

  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_written), stored));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(updated, idx_other), init));

  REQUIRE(solver->check() == camada::checkResult::SAT);

  auto read_written = solver->getArrayElement(updated, idx_written);
  auto read_other = solver->getArrayElement(updated, idx_other);

  REQUIRE(read_written->Sort == boolsort);
  REQUIRE(read_other->Sort == boolsort);
  auto read_written_res = solver->getBool(read_written);
  auto read_other_res = solver->getBool(read_other);
  REQUIRE(read_written_res);
  REQUIRE(read_other_res);
  REQUIRE(read_written_res.value());
  REQUIRE(!read_other_res.value());
}

// Pin that a const-array constructed inside a (push) scope still satisfies
// its defining equality after a matching (pop). The SMT-LIB backend used to
// lower mkArrayConst through (declare-fun) + (assert (= sym ...)), and the
// asserted equality was scoped — the symbol survived the pop with no
// constraint, leaving the array silently unconstrained. The current
// encoding uses (define-fun), which is permanent under
// :global-declarations true.
inline void array_const_survives_push_pop(const camada::SMTSolverRef &solver) {
  {
    auto idx = solver->mkBVSort(3);
    auto elem = solver->mkBVSort(8);
    auto fill = solver->mkBVFromDec(170, elem); // 0b10101010

    solver->push();
    auto a = solver->mkArrayConst(idx, fill);
    solver->pop();

    // After the pop, the const-array reference is still in effect: every
    // index reads back the fill value.
    auto sample_idx = solver->mkBVFromDec(3, idx);
    solver->addConstraint(
        solver->mkEqual(solver->mkArraySelect(a, sample_idx), fill));
    REQUIRE(solver->check() == camada::checkResult::SAT);
  }

  // Reset and re-establish every handle from scratch — handles created
  // before reset() are stale.
  solver->reset();

  {
    auto idx = solver->mkBVSort(3);
    auto elem = solver->mkBVSort(8);
    auto fill = solver->mkBVFromDec(170, elem);

    solver->push();
    auto a = solver->mkArrayConst(idx, fill);
    solver->pop();

    auto sample_idx = solver->mkBVFromDec(3, idx);
    // Constraining a different value at the same index must be unsat —
    // confirms the const-array binding is still in force after the pop.
    solver->addConstraint(solver->mkNot(
        solver->mkEqual(solver->mkArraySelect(a, sample_idx), fill)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }
}

// Semantics that only the lazy constant-array lowering can provide: a
// 64-bit index domain is impossible to materialize store-per-index. Runs on
// solvers whose nativeConstArraySupport() is false (or overridden to false
// in the regression suite).
inline void lazy_const_array_semantics(const camada::SMTSolverRef &solver) {
  {
    auto idx = solver->mkBVSort(64);
    auto elem = solver->mkBVSort(8);
    auto init = solver->mkBVFromDec(0, elem);
    auto stored = solver->mkBVFromDec(9, elem);

    auto arr = solver->mkArrayConst(idx, init);
    REQUIRE(arr->getKind() == camada::SMTExprKind::ArrayConst);

    // Every element of store(arr, k, 9) is 0 or 9, even at symbolic
    // positions: the default must chase the index wherever the solver
    // puts it.
    auto k = solver->mkSymbol("lca_k", idx);
    auto i = solver->mkSymbol("lca_i", idx);
    auto updated = solver->mkArrayStore(arr, k, stored);
    auto x = solver->mkArraySelect(updated, i);
    solver->addConstraint(solver->mkNot(solver->mkEqual(x, init)));
    solver->addConstraint(solver->mkNot(solver->mkEqual(x, stored)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }

  solver->reset();

  {
    auto idx = solver->mkBVSort(64);
    auto elem = solver->mkBVSort(8);
    auto init = solver->mkBVFromDec(0, elem);
    auto stored = solver->mkBVFromDec(9, elem);

    auto arr = solver->mkArrayConst(idx, init);
    auto idx_written = solver->mkBVFromDec(5, idx);
    auto idx_untouched = solver->mkBVFromDec(7, idx);
    auto updated = solver->mkArrayStore(arr, idx_written, stored);

    solver->addConstraint(
        solver->mkEqual(solver->mkArraySelect(updated, idx_written), stored));
    REQUIRE(solver->check() == camada::checkResult::SAT);

    // The model query at an index the formula never touched must still
    // report the default, resolved from the tracked derivation chain.
    auto read_written = solver->getArrayElement(updated, idx_written);
    auto read_untouched = solver->getArrayElement(updated, idx_untouched);
    auto read_written_res = solver->getBVInBin(read_written);
    auto read_untouched_res = solver->getBVInBin(read_untouched);
    REQUIRE(read_written_res);
    REQUIRE(read_untouched_res);
    REQUIRE(read_written_res.value() == "00001001");
    REQUIRE(read_untouched_res.value() == "00000000");
  }
}
