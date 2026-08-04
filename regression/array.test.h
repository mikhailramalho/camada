
#include "camada.h"

#include <bitset>
#include <catch2/catch_test_macros.hpp>

inline void
array(const camada::SMTSolverRef &solver,
      camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  // An array
  auto indexsort = solver->mkBVSort(2);
  auto elemsort = solver->mkBVSort(10);
  auto init = solver->mkBVFromDec(5, 10);
  REQUIRE(init->getKind() == camada::SMTExprKind::BVConst);
  auto arr = solver->mkArrayConst(indexsort, init, Lowering);
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

inline void array_const_store_semantics(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto indexsort = solver->mkBVSort(3);
  auto elemsort = solver->mkBVSort(8);

  auto init = solver->mkBVFromDec(170, elemsort);
  auto stored = solver->mkBVFromDec(17, elemsort);
  auto idx_written = solver->mkBVFromDec(3, indexsort);
  auto idx_other = solver->mkBVFromDec(5, indexsort);

  auto arr = solver->mkArrayConst(indexsort, init, Lowering);
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

inline void bool_array_const_store_semantics(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto indexsort = solver->mkBVSort(2);
  auto boolsort = solver->mkBoolSort();

  auto init = solver->mkBool(false);
  auto stored = solver->mkBool(true);
  auto idx_written = solver->mkBVFromDec(1, indexsort);
  auto idx_other = solver->mkBVFromDec(2, indexsort);

  auto arr = solver->mkArrayConst(indexsort, init, Lowering);
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
inline void array_const_survives_push_pop(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  {
    auto idx = solver->mkBVSort(3);
    auto elem = solver->mkBVSort(8);
    auto fill = solver->mkBVFromDec(170, elem); // 0b10101010

    solver->push();
    auto a = solver->mkArrayConst(idx, fill, Lowering);
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
    auto a = solver->mkArrayConst(idx, fill, Lowering);
    solver->pop();

    auto sample_idx = solver->mkBVFromDec(3, idx);
    // Constraining a different value at the same index must be unsat —
    // confirms the const-array binding is still in force after the pop.
    solver->addConstraint(solver->mkNot(
        solver->mkEqual(solver->mkArraySelect(a, sample_idx), fill)));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  }
}

// Constant-array semantics over a 64-bit index domain — impossible to
// materialize store-per-index, so this exercises native constant arrays on
// capable backends and the lazy lowering elsewhere (STP).
inline void wide_index_const_array_semantics(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  {
    auto idx = solver->mkBVSort(64);
    auto elem = solver->mkBVSort(8);
    auto init = solver->mkBVFromDec(0, elem);
    auto stored = solver->mkBVFromDec(9, elem);

    auto arr = solver->mkArrayConst(idx, init, Lowering);
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

    auto arr = solver->mkArrayConst(idx, init, Lowering);
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

// Pin the scope-escape case: a select over a constant array built inside a
// push scope and asserted only after the pop. Trivial for native constant
// arrays; under the lazy lowering the default axiom asserted at
// construction time is popped with the scope, so journaled constraints
// must be re-asserted at the outer level.
inline void const_array_select_survives_pop(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto idx = solver->mkBVSort(64);
  auto elem = solver->mkBVSort(8);
  auto init = solver->mkBVFromDec(0, elem);

  auto arr = solver->mkArrayConst(idx, init, Lowering);
  auto i = solver->mkSymbol("lcasp_i", idx);

  solver->push();
  auto sel = solver->mkArraySelect(arr, i); // default asserted in the scope
  solver->pop();

  // The handle outlives the pop; the default must still bind it.
  solver->addConstraint(solver->mkNot(solver->mkEqual(sel, init)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// The lowerings interoperate: lazily and natively (or Auto-) lowered
// constant arrays share array sorts and can appear in one formula.
// Shared decoder for the array-model tests below: the model value at an
// index is the first entry whose index matches, else the base, which must
// then exist.
inline int64_t array_model_value_at(const camada::SMTSolverRef &solver,
                                    const camada::ArrayModel &Model,
                                    int64_t Index) {
  for (const auto &Entry : Model.Entries) {
    auto IndexValue = solver->getBV(Entry.first);
    REQUIRE(IndexValue);
    if (IndexValue.value() == Index) {
      auto ElemValue = solver->getBV(Entry.second);
      REQUIRE(ElemValue);
      return ElemValue.value();
    }
  }
  REQUIRE(Model.Base);
  auto BaseValue = solver->getBV(Model.Base);
  REQUIRE(BaseValue);
  return BaseValue.value();
}

inline void array_model_values(const camada::SMTSolverRef &solver) {
  auto indexsort = solver->mkBVSort(8);
  auto arr = solver->mkSymbol("arr", solver->mkArraySort(indexsort, indexsort));
  auto idx = [&](int64_t V) { return solver->mkBVFromDec(V, 8); };
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(arr, idx(1)), idx(10)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(arr, idx(2)), idx(20)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  auto Model = solver->getArrayValues(arr);
  if (!Model) {
    REQUIRE(Model.error().Code == camada::SMTErrorCode::UnsupportedOperation);
    return;
  }
  REQUIRE(array_model_value_at(solver, Model.value(), 1) == 10);
  REQUIRE(array_model_value_at(solver, Model.value(), 2) == 20);
}

inline void const_array_model_values(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto indexsort = solver->mkBVSort(8);
  auto idx = [&](int64_t V) { return solver->mkBVFromDec(V, 8); };
  auto arr = solver->mkArrayConst(indexsort, idx(7), Lowering);
  arr = solver->mkArrayStore(arr, idx(3), idx(9));
  arr = solver->mkArrayStore(arr, idx(3), idx(11)); // shadows the store of 9
  // Touch the array so every backend has it in the formula.
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(arr, idx(0)), idx(7)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  auto Model = solver->getArrayValues(arr);
  if (!Model) {
    REQUIRE(Model.error().Code == camada::SMTErrorCode::UnsupportedOperation);
    return;
  }
  // First matching entry wins: the outermost store shadows the inner one.
  REQUIRE(array_model_value_at(solver, Model.value(), 3) == 11);
  // Indexes never mentioned in the formula must read the initializer,
  // through the base or an explicit entry.
  REQUIRE(array_model_value_at(solver, Model.value(), 200) == 7);
  // The sparse model must agree with the per-index query API.
  auto Probe = solver->getBV(solver->getArrayElement(arr, idx(200)));
  REQUIRE(Probe);
  REQUIRE(Probe.value() == 7);
}

// Plain array equality must be extensional in both polarities. The
// asserted-positive direction is the regression: STP's old lowering
// (select(A,w) == select(B,w) at one fresh index) only constrained one
// cell, so `a == b` plus disagreeing selects was satisfiable.
inline void array_equality_semantics(const camada::SMTSolverRef &solver) {
  auto mk = [&](const char *NameA, const char *NameB) {
    auto indexsort = solver->mkBVSort(8);
    auto arrsort = solver->mkArraySort(indexsort, indexsort);
    return std::make_pair(solver->mkSymbol(NameA, arrsort),
                          solver->mkSymbol(NameB, arrsort));
  };
  auto idx = [&](int64_t V) { return solver->mkBVFromDec(V, 8); };

  // Positive direction: equality forces agreement at observed indexes.
  auto [a, b] = mk("a", "b");
  solver->addConstraint(solver->mkEqual(a, b));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(a, idx(0)), idx(1)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(b, idx(0)), idx(2)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Same, with the selects observed BEFORE the equality is built — pins
  // the replay of already-observed indexes.
  solver->reset();
  auto [c, d] = mk("c", "d");
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(c, idx(0)), idx(1)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(d, idx(0)), idx(2)));
  solver->addConstraint(solver->mkEqual(c, d));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Negative direction stays satisfiable: a difference can be exhibited.
  solver->reset();
  auto [e, f] = mk("e", "f");
  solver->addConstraint(solver->mkNot(solver->mkEqual(e, f)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Agreeing constraints under asserted equality are satisfiable.
  solver->reset();
  auto [g, h] = mk("g", "h");
  solver->addConstraint(solver->mkEqual(g, h));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(g, idx(0)), idx(5)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(h, idx(0)), idx(5)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Equality must be visible through store-derived terms: reading
  // store(a, j, v) at i != j reads a at i.
  solver->reset();
  auto [p, q] = mk("p", "q");
  solver->addConstraint(solver->mkEqual(p, q));
  auto ps = solver->mkArrayStore(p, idx(1), idx(42));
  auto qs = solver->mkArrayStore(q, idx(1), idx(42));
  solver->addConstraint(solver->mkNot(solver->mkEqual(
      solver->mkArraySelect(ps, idx(0)), solver->mkArraySelect(qs, idx(0)))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // ... and through ite-derived terms.
  solver->reset();
  auto [r, s] = mk("r", "s");
  auto cond = solver->mkSymbol("cond", solver->mkBoolSort());
  solver->addConstraint(solver->mkEqual(r, s));
  auto i1 = solver->mkIte(cond, r, s);
  auto i2 = solver->mkIte(cond, s, r);
  solver->addConstraint(solver->mkNot(
      solver->mkEqual(solver->mkArraySelect(i1, solver->mkBVFromDec(0, 8)),
                      solver->mkArraySelect(i2, solver->mkBVFromDec(0, 8)))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Transitive chains close through observed-index congruence.
  solver->reset();
  auto [t, u] = mk("t", "u");
  auto v = solver->mkSymbol("v", t->Sort);
  solver->addConstraint(solver->mkEqual(t, u));
  solver->addConstraint(solver->mkEqual(u, v));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(t, idx(0)), idx(1)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(v, idx(0)), idx(2)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Polarity safety: the equality literal used under boolean structure.
  solver->reset();
  auto [w, x] = mk("w", "x");
  auto flag = solver->mkSymbol("flag", solver->mkBoolSort());
  auto eq = solver->mkEqual(w, x);
  solver->addConstraint(solver->mkIte(flag, eq, solver->mkNot(eq)));
  solver->addConstraint(flag);
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(w, idx(0)), idx(1)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(x, idx(0)), idx(2)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// Equality between an array symbol and a constant array — ESBMC's
// `symbol = array_of(v)` pattern. Bitwuzla 0.9.x answers UNKNOWN on the
// native ((as const ...)) form of this (with an "Equality over constant
// arrays not fully supported yet" warning), which is why it lowers
// constant arrays lazily; this fixture pins the pattern on every
// backend and lowering.
inline void const_array_equality_semantics(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto indexsort = solver->mkBVSort(8);
  auto idx = [&](int64_t V) { return solver->mkBVFromDec(V, 8); };
  auto arrsort = solver->mkArraySort(indexsort, indexsort);

  auto a = solver->mkSymbol("a", arrsort);
  solver->addConstraint(
      solver->mkEqual(a, solver->mkArrayConst(indexsort, idx(7), Lowering)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(a, idx(3)), idx(7)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // reset() invalidates every handle; rebuild the sorts for the
  // contradiction direction.
  solver->reset();
  indexsort = solver->mkBVSort(8);
  arrsort = solver->mkArraySort(indexsort, indexsort);
  auto b = solver->mkSymbol("b", arrsort);
  solver->addConstraint(
      solver->mkEqual(b, solver->mkArrayConst(indexsort, idx(7), Lowering)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(b, idx(3)), idx(9)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Derived-before-equality: a store built over the symbol BEFORE the
  // constant-array equality exists must still see the default at indexes
  // the store does not shadow.
  solver->reset();
  indexsort = solver->mkBVSort(8);
  arrsort = solver->mkArraySort(indexsort, indexsort);
  auto c = solver->mkSymbol("c", arrsort);
  auto cs = solver->mkArrayStore(c, idx(1), idx(42));
  solver->addConstraint(
      solver->mkEqual(c, solver->mkArrayConst(indexsort, idx(7), Lowering)));
  solver->addConstraint(
      solver->mkEqual(solver->mkArraySelect(cs, idx(3)), idx(9)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// A symbol array equated to one lazy const array, then disequated from a
// second — exercises the encoded-equality witness over an operand that is
// itself a plain symbol equated (via a separate encoded equality) to a
// lazy root. The disequality's witness is unobserved, so the symbol=root
// congruence does not bind there: the model must be free to exhibit a real
// difference, yet a forced agreement at a concrete index must still hold.
inline void lazy_array_transitive_equality(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto bv8 = solver->mkBVSort(8);
  auto idx = [&](int64_t V) { return solver->mkBVFromDec(V, 8); };
  auto arrsort = solver->mkArraySort(bv8, bv8);

  // B = array_of(7); C = array_of(9); B != C is satisfiable (they differ
  // at every index, exhibitable at the disequality's own witness).
  auto b = solver->mkSymbol("lat_b", arrsort);
  auto c = solver->mkSymbol("lat_c", arrsort);
  solver->addConstraint(
      solver->mkEqual(b, solver->mkArrayConst(bv8, idx(7), Lowering)));
  solver->addConstraint(
      solver->mkEqual(c, solver->mkArrayConst(bv8, idx(9), Lowering)));
  solver->addConstraint(solver->mkNot(solver->mkEqual(b, c)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // But B's value is still pinned: reading B at any index must be 7, even
  // though B != C let the solver pick a witness where B and C differ.
  solver->reset();
  bv8 = solver->mkBVSort(8);
  arrsort = solver->mkArraySort(bv8, bv8);
  auto b2 = solver->mkSymbol("lat_b2", arrsort);
  auto c2 = solver->mkSymbol("lat_c2", arrsort);
  solver->addConstraint(
      solver->mkEqual(b2, solver->mkArrayConst(bv8, idx(7), Lowering)));
  solver->addConstraint(
      solver->mkEqual(c2, solver->mkArrayConst(bv8, idx(9), Lowering)));
  solver->addConstraint(solver->mkNot(solver->mkEqual(b2, c2)));
  auto m = solver->mkSymbol("lat_m", bv8);
  solver->addConstraint(
      solver->mkNot(solver->mkEqual(solver->mkArraySelect(b2, m), idx(7))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// Constant array whose initializer is itself a constant array —
// array_of(array_of(v)), ESBMC's multidimensional `array_of`. On native
// constant-array backends the inner const array is just an array-sorted
// element; on lazy backends both levels lower lazily, so the outer
// default axiom is an array equality between select(outer, i) and the
// inner lazy root. This pins read-through, store-over-inner, the
// negative direction, equality propagation, and model round-trip.
inline void nested_const_array_semantics(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto bv8 = solver->mkBVSort(8);
  auto idx = [&](int64_t V) { return solver->mkBVFromDec(V, 8); };
  auto innerSort = solver->mkArraySort(bv8, bv8);

  // Default read-through: every cell of the outer array is the inner
  // const array, whose every cell is v. So select(select(outer,i),j)==v.
  auto inner = solver->mkArrayConst(bv8, idx(7), Lowering);
  auto outer = solver->mkArrayConst(bv8, inner, Lowering);
  REQUIRE(outer->Sort->getElementSort() == innerSort);
  auto i = solver->mkSymbol("i", bv8);
  auto j = solver->mkSymbol("j", bv8);
  auto deep = solver->mkArraySelect(solver->mkArraySelect(outer, i), j);
  solver->addConstraint(solver->mkNot(solver->mkEqual(deep, idx(7))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Store into the inner array at a concrete index, read elsewhere: the
  // written cell holds the stored value, every other cell the default.
  solver->reset();
  bv8 = solver->mkBVSort(8);
  inner = solver->mkArrayConst(bv8, idx(7), Lowering);
  auto innerStored = solver->mkArrayStore(inner, idx(2), idx(99));
  auto k = solver->mkSymbol("k", bv8);
  solver->addConstraint(solver->mkNot(solver->mkEqual(k, idx(2))));
  auto ok = solver->mkAnd(
      solver->mkEqual(solver->mkArraySelect(innerStored, idx(2)), idx(99)),
      solver->mkEqual(solver->mkArraySelect(innerStored, k), idx(7)));
  solver->addConstraint(solver->mkNot(ok));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Negative direction must stay satisfiable: a deep read equal to a
  // value different from the default is impossible, but equal to the
  // default is fine — no false UNSAT, and no spurious model either.
  solver->reset();
  bv8 = solver->mkBVSort(8);
  inner = solver->mkArrayConst(bv8, idx(7), Lowering);
  outer = solver->mkArrayConst(bv8, inner, Lowering);
  i = solver->mkSymbol("i2", bv8);
  j = solver->mkSymbol("j2", bv8);
  deep = solver->mkArraySelect(solver->mkArraySelect(outer, i), j);
  solver->addConstraint(solver->mkEqual(deep, idx(7)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  solver->reset();
  bv8 = solver->mkBVSort(8);
  inner = solver->mkArrayConst(bv8, idx(7), Lowering);
  outer = solver->mkArrayConst(bv8, inner, Lowering);
  i = solver->mkSymbol("i3", bv8);
  j = solver->mkSymbol("j3", bv8);
  deep = solver->mkArraySelect(solver->mkArraySelect(outer, i), j);
  solver->addConstraint(solver->mkEqual(deep, idx(8))); // != default 7
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Equality propagation: two equal nested const arrays agree on a deep
  // read even when one side was derived before the equality.
  solver->reset();
  bv8 = solver->mkBVSort(8);
  innerSort = solver->mkArraySort(bv8, bv8);
  auto outerSort = solver->mkArraySort(bv8, innerSort);
  auto a = solver->mkSymbol("a", outerSort);
  i = solver->mkSymbol("i4", bv8);
  j = solver->mkSymbol("j4", bv8);
  auto aDeep = solver->mkArraySelect(solver->mkArraySelect(a, i), j);
  solver->addConstraint(solver->mkEqual(
      a, solver->mkArrayConst(bv8, solver->mkArrayConst(bv8, idx(5), Lowering),
                              Lowering)));
  solver->addConstraint(solver->mkNot(solver->mkEqual(aDeep, idx(5))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);

  // Model round-trip: getArrayElement on the outer returns an inner
  // array whose deep read matches the default.
  solver->reset();
  bv8 = solver->mkBVSort(8);
  inner = solver->mkArrayConst(bv8, idx(7), Lowering);
  outer = solver->mkArrayConst(bv8, inner, Lowering);
  // Touch a deep cell so the array is in the formula on every backend.
  solver->addConstraint(solver->mkEqual(
      solver->mkArraySelect(solver->mkArraySelect(outer, idx(0)), idx(0)),
      idx(7)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  auto innerModel = solver->getArrayElement(outer, idx(1));
  REQUIRE(innerModel->Sort == solver->mkArraySort(bv8, bv8));
  auto cell = solver->getBV(solver->getArrayElement(innerModel, idx(3)));
  REQUIRE(cell);
  REQUIRE(cell.value() == 7);

  // Adversarial: two independent inner-array disequalities must each be
  // exhibitable at their OWN witness index — a shared witness would
  // conflate them and force a spurious UNSAT. Each equality's negative
  // witness is fresh, so this stays SAT.
  solver->reset();
  bv8 = solver->mkBVSort(8);
  innerSort = solver->mkArraySort(bv8, bv8);
  auto m1 = solver->mkSymbol("m1", innerSort);
  auto n1 = solver->mkSymbol("n1", innerSort);
  auto m2 = solver->mkSymbol("m2", innerSort);
  auto n2 = solver->mkSymbol("n2", innerSort);
  solver->addConstraint(solver->mkNot(solver->mkEqual(m1, n1)));
  solver->addConstraint(solver->mkNot(solver->mkEqual(m2, n2)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Adversarial negative direction with a lazy const array: a difference
  // claimed against the default must be a real one. select(outer,i) is the
  // inner const array (all 7s); claiming select(select(outer,i),j) == 4 is
  // impossible, but the model must not fabricate a difference at an
  // unobserved index — pinned by the witness default. UNSAT.
  solver->reset();
  bv8 = solver->mkBVSort(8);
  inner = solver->mkArrayConst(bv8, idx(7), Lowering);
  outer = solver->mkArrayConst(bv8, inner, Lowering);
  auto sym = solver->mkSymbol("sym", solver->mkArraySort(bv8, bv8));
  i = solver->mkSymbol("i5", bv8);
  // sym equals the inner const array, but disagrees with it at j: UNSAT,
  // because sym = select(outer,i) = inner forces agreement everywhere
  // observed.
  solver->addConstraint(solver->mkEqual(sym, solver->mkArraySelect(outer, i)));
  auto j5 = solver->mkSymbol("j5", bv8);
  solver->addConstraint(
      solver->mkNot(solver->mkEqual(solver->mkArraySelect(sym, j5), idx(7))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

// nested_const_array_semantics inside a pushed scope: the deep default
// asserted in the scope must still bind handles that outlive the pop.
inline void nested_const_array_survives_pop(
    const camada::SMTSolverRef &solver,
    camada::ConstArrayLowering Lowering = camada::ConstArrayLowering::Auto) {
  auto bv8 = solver->mkBVSort(8);
  auto idx = [&](int64_t V) { return solver->mkBVFromDec(V, 8); };
  auto inner = solver->mkArrayConst(bv8, idx(7), Lowering);
  auto outer = solver->mkArrayConst(bv8, inner, Lowering);
  auto i = solver->mkSymbol("ncsp_i", bv8);
  auto j = solver->mkSymbol("ncsp_j", bv8);

  solver->push();
  auto deep = solver->mkArraySelect(solver->mkArraySelect(outer, i), j);
  solver->pop();

  solver->addConstraint(solver->mkNot(solver->mkEqual(deep, idx(7))));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}

inline void const_array_lowering_interop(const camada::SMTSolverRef &solver) {
  auto idx = solver->mkBVSort(8);
  auto elem = solver->mkBVSort(8);
  auto zero = solver->mkBVFromDec(0, elem);
  auto one = solver->mkBVFromDec(1, elem);

  auto lazy = solver->mkArrayConst(idx, zero, camada::ConstArrayLowering::Lazy);
  auto other = solver->mkArrayConst(idx, one, camada::ConstArrayLowering::Auto);
  REQUIRE(lazy->getKind() == camada::SMTExprKind::ArrayConst);
  REQUIRE(lazy->Sort == other->Sort);

  // select(lazy, i) + select(other, i) == 1 at every index.
  auto i = solver->mkSymbol("cali_i", idx);
  auto sum = solver->mkBVAdd(solver->mkArraySelect(lazy, i),
                             solver->mkArraySelect(other, i));
  solver->addConstraint(solver->mkNot(solver->mkEqual(sum, one)));
  REQUIRE(solver->check() == camada::checkResult::UNSAT);
}
