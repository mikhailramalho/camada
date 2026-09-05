
#include "camada.h"

#include <bitset>
#include <catch2/catch_test_macros.hpp>
#include <string>
#include <vector>

inline void equal_ten(const camada::SMTSolverRef &solver) {
  // A free variable
  auto f = solver->mkSymbol("f", solver->mkBVSort(10));
  REQUIRE(f->getKind() == camada::SMTExprKind::Symbol);

  // And assert if there is a value for 'f' that is equal to 10
  auto ten = solver->mkBVFromBin(std::bitset<10>(-10).to_string(), 10);
  REQUIRE(ten->getKind() == camada::SMTExprKind::BVConst);
  auto eq = solver->mkEqual(f, ten);
  REQUIRE(eq->getKind() == camada::SMTExprKind::Equal);

  // Add the constraint to the solver
  solver->addConstraint(eq);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto f_res = solver->getBV(f);
  REQUIRE(f_res);
  REQUIRE(f_res.value() == -10);
  auto ten_res = solver->getBV(ten);
  REQUIRE(ten_res);
  REQUIRE(f_res.value() == ten_res.value());
}

inline void fp_equal(const camada::SMTSolverRef &solver,
                     camada::FPEncoding Encoding) {
  auto x = solver->mkFP32(0.06f, Encoding);
  auto y = solver->mkFP64(-7.0, Encoding);
  REQUIRE(x->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(y->getKind() == camada::SMTExprKind::FPConst);

  auto fx = solver->mkSymbol("fx", solver->mkFP32Sort(Encoding));
  auto fy = solver->mkSymbol("fy", solver->mkFP64Sort(Encoding));
  REQUIRE(fx->getKind() == camada::SMTExprKind::Symbol);
  REQUIRE(fy->getKind() == camada::SMTExprKind::Symbol);

  // Add the constraint to the solver
  auto eqy = solver->mkEqual(fy, y);
  auto eqx = solver->mkEqual(fx, x);
  REQUIRE(eqy->getKind() == camada::SMTExprKind::Equal);
  REQUIRE(eqx->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(eqy);
  solver->addConstraint(eqx);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  auto fx_res = solver->getFP32(fx);
  auto fy_res = solver->getFP64(fy);
  REQUIRE(fx_res);
  REQUIRE(fy_res);
  REQUIRE(fx_res.value() == 0.06f);
  REQUIRE(fy_res.value() == -7.0);
}

inline void implies_semantics(const camada::SMTSolverRef &solver) {
  auto f1 = solver->mkBool(false);
  auto implication = solver->mkImplies(f1, f1);
  REQUIRE(f1->getKind() == camada::SMTExprKind::BoolConst);
  REQUIRE(implication->getKind() == camada::SMTExprKind::Implies);
  solver->addConstraint(solver->mkNot(implication));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
}

inline void implies_true_implies_false(const camada::SMTSolverRef &solver) {
  auto t = solver->mkBool(true);
  auto f = solver->mkBool(false);
  REQUIRE(t->getKind() == camada::SMTExprKind::BoolConst);
  REQUIRE(f->getKind() == camada::SMTExprKind::BoolConst);
  auto implication = solver->mkImplies(t, f);
  REQUIRE(implication->getKind() == camada::SMTExprKind::Implies);
  solver->addConstraint(implication);
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
}

// Clears a per-check wall-clock limit on the way out. The limit survives
// reset() by design and RESETANDTEST only resets, so a fixture that leaves
// one set leaks it into every fixture after it -- a REQUIRE failure would
// then bury itself under unrelated UNKNOWNs.
struct TimeoutGuard {
  const camada::SMTSolverRef &S;
  ~TimeoutGuard() { S->setTimeout(0); }
};

// Asserts that Prefix_p * Prefix_q is a 64-bit semiprime, with both factors
// above one. The 128-bit extension rules out wrap-around shortcuts, so the
// query is far beyond any small time budget on every backend -- the standard
// way these fixtures force a deterministic UNKNOWN.
inline camada::SMTExprRef
assert_semiprime_factoring(const camada::SMTSolverRef &solver,
                           const std::string &Prefix) {
  auto p = solver->mkSymbol(Prefix + "_p", solver->mkBVSort(64));
  auto q = solver->mkSymbol(Prefix + "_q", solver->mkBVSort(64));
  constexpr uint64_t Semiprime = 4294967291ULL * 4294967279ULL;
  auto prod =
      solver->mkBVMul(solver->mkBVZeroExt(p, 64), solver->mkBVZeroExt(q, 64));
  auto k = solver->mkBVZeroExt(
      solver->mkBVFromDec(static_cast<int64_t>(Semiprime), 64), 64);
  solver->addConstraint(solver->mkEqual(prod, k));
  auto one = solver->mkBVFromDec(1, 64);
  solver->addConstraint(solver->mkBVUgt(p, one));
  solver->addConstraint(solver->mkBVUgt(q, one));
  return p; // the caller may constrain a factor further
}

inline void unknown_reason_semantics(const camada::SMTSolverRef &solver) {
  // Nothing has answered UNKNOWN yet.
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::NotApplicable);

  auto x = solver->mkSymbol("ur_x", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(3, 8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  // A decided check clears any earlier reason rather than leaving it to
  // be misread as belonging to this one.
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::NotApplicable);

  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(4, 8)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::NotApplicable);

  // A reason must not outlive the query it belonged to: reasonUnknown() is
  // documented to report NotApplicable at any time other than right after
  // an UNKNOWN check, but only reset() used to clear it, so a mutation
  // after an UNKNOWN left a stale Timeout for a query that never ran.
  solver->reset();
  if (solver->setTimeout(150)) {
    TimeoutGuard ClearTimeout{solver};
    auto p = assert_semiprime_factoring(solver, "ur");
    if (solver->check() == camada::CheckResult::UNKNOWN) {
      REQUIRE(solver->reasonUnknown() != camada::UnknownReason::NotApplicable);
      solver->addConstraint(solver->mkBVUgt(p, solver->mkBVFromDec(2, 64)));
      REQUIRE(solver->reasonUnknown() == camada::UnknownReason::NotApplicable);
    }
  }
}

inline void solver_timeout_semantics(const camada::SMTSolverRef &solver) {
  if (!solver->setTimeout(150)) {
    // Backends without enforceable limits must report so and stay usable.
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::CheckResult::SAT);
    return;
  }

  // A generous limit must not affect an easy query.
  auto x = solver->mkSymbol("x", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(7, 8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  // Factoring a 64-bit semiprime exactly (the 128-bit extension rules out
  // wrap-around shortcuts) is far beyond a 150ms budget on every backend,
  // so the limit must turn the query into UNKNOWN instead of a hang. The
  // resets also pin that the limit itself survives reset().
  auto assertSemiprimeFactoring = [&]() {
    solver->reset();
    (void)assert_semiprime_factoring(solver, "st");
  };
  assertSemiprimeFactoring();
  REQUIRE(solver->check() == camada::CheckResult::UNKNOWN);
  // The UNKNOWN is the limit firing, not the solver giving up.
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::Timeout);

  // The limit applies to assumption-based checks too. Rebuild the problem
  // from scratch first: an incremental solver resumes the interrupted
  // search with everything it already learned, and the cumulative budget
  // was occasionally enough to actually factor the semiprime (seen with
  // bitwuzla), turning this deterministic UNKNOWN into a flaky SAT.
  assertSemiprimeFactoring();
  auto t = solver->mkSymbol("t", solver->mkBoolSort());
  REQUIRE(solver->checkSatAssuming({t}) == camada::CheckResult::UNKNOWN);
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::Timeout);

  // Clearing the limit must work from the just-timed-out state.
  REQUIRE(solver->setTimeout(0));

  // A timed-out check must leave the solver fully usable WITHOUT a reset:
  // new constraints must take effect and incremental scopes must work. A
  // backend whose interrupted context goes stale would drop the assert
  // and answer instantly from the poisoned state instead of UNSAT.
  solver->push();
  solver->addConstraint(solver->mkBool(false));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  solver->pop();

  // Normal solving works again after the limit is cleared.
  solver->reset();
  auto y = solver->mkSymbol("y", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(y, solver->mkBVFromDec(9, 8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void check_sat_assuming_semantics(const camada::SMTSolverRef &solver) {
  auto a = solver->mkSymbol("a", solver->mkBoolSort());
  auto b = solver->mkSymbol("b", solver->mkBoolSort());
  solver->addConstraint(solver->mkOr(a, b));

  // Assuming both false contradicts (or a b).
  const std::vector<camada::SMTExprRef> negBoth = {solver->mkNot(a),
                                                   solver->mkNot(b)};
  REQUIRE(solver->checkSatAssuming(negBoth) == camada::CheckResult::UNSAT);

  auto core = solver->getUnsatAssumptions();
  if (core) {
    // The core must be a non-empty subset that is itself sufficient:
    // re-checking under only the returned assumptions stays UNSAT.
    REQUIRE(!core.value().empty());
    REQUIRE(solver->checkSatAssuming(core.value()) ==
            camada::CheckResult::UNSAT);
  } else {
    REQUIRE(core.error().Code == camada::SMTErrorCode::UnsupportedOperation);
  }

  // A compound (non-literal) assumption must work too — backends whose
  // native API only accepts literals lower it through activation literals.
  REQUIRE(solver->checkSatAssuming({solver->mkNot(solver->mkOr(a, b))}) ==
          camada::CheckResult::UNSAT);

  // Assumptions are per-query: they do not persist into later checks.
  REQUIRE(solver->checkSatAssuming({a}) == camada::CheckResult::SAT);
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  // After a check that was not an UNSAT checkSatAssuming, the unsat
  // assumptions are stale and querying them is an error.
  REQUIRE(!solver->getUnsatAssumptions());

  // Mutating the solver state after an UNSAT checkSatAssuming also
  // invalidates the unsat assumptions.
  REQUIRE(solver->checkSatAssuming(negBoth) == camada::CheckResult::UNSAT);
  solver->push();
  REQUIRE(!solver->getUnsatAssumptions());
  solver->pop();

  // An empty assumption set degenerates to a plain check.
  REQUIRE(solver->checkSatAssuming({}) == camada::CheckResult::SAT);
}

// Extending by zero bits is a no-op, not an error: callers compute the
// extension width arithmetically and a degenerate zero is normal. The STP
// backend used to build a zero-width constant here and abort.
inline void bv_extend_by_zero_semantics(const camada::SMTSolverRef &solver) {
  auto v = solver->mkBVFromBin("1010", 4);
  auto z = solver->mkBVZeroExt(v, 0);
  auto s = solver->mkBVSignExt(v, 0);
  REQUIRE(z->getWidth() == 4);
  REQUIRE(s->getWidth() == 4);
  solver->addConstraint(
      solver->mkAnd(solver->mkEqual(z, v), solver->mkEqual(s, v)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// bvsrem takes the sign of the DIVIDEND and bvsdiv truncates toward zero
// (SMT-LIB), which differ from the modulo convention whenever the operand
// signs disagree: -7 srem 2 is -1, not +1. The STP backend used to call
// STP's modulo routine here and silently returned the divisor's sign.
inline void bv_signed_div_rem_semantics(const camada::SMTSolverRef &solver) {
  auto d = [&](int64_t V) { return solver->mkBVFromDec(V, 32); };
  struct Case {
    int64_t A, B, SDiv, SRem;
  };
  const Case Cases[] = {
      {-7, 2, -3, -1}, {7, -2, -3, 1}, {-7, -2, 3, -1}, {7, 2, 3, 1}};
  camada::SMTExprRef All = solver->mkBool(true);
  for (const Case &C : Cases)
    All = solver->mkAnd(
        All, solver->mkAnd(
                 solver->mkEqual(solver->mkBVSDiv(d(C.A), d(C.B)), d(C.SDiv)),
                 solver->mkEqual(solver->mkBVSRem(d(C.A), d(C.B)), d(C.SRem))));
  solver->addConstraint(All);
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void bv_lshr_semantics(const camada::SMTSolverRef &solver) {
  auto value = solver->mkBVFromBin("1000", 4);
  auto shift = solver->mkBVFromDec(1, 4);
  auto result = solver->mkBVLshr(value, shift);
  REQUIRE(value->getKind() == camada::SMTExprKind::BVConst);
  REQUIRE(shift->getKind() == camada::SMTExprKind::BVConst);
  REQUIRE(result->getKind() == camada::SMTExprKind::BVLshr);

  solver->addConstraint(
      solver->mkEqual(result, solver->mkBVFromBin("0100", 4)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// Prove each overflow predicate equivalent to an independent reference
// encoding for symbolic operands. Every reference computes the exact result
// at a wider width and range-checks it — deliberately a different
// formulation from both the native solver predicates and the common-layer
// fallback, so a bug on either side makes the equivalence SAT. Width 1 is
// included because it is where sign-bit extracts and extensions are most
// fragile.
inline void bv_overflow_semantics(const camada::SMTSolverRef &solver) {
  for (const unsigned W : {1u, 8u}) {
    const int64_t SMax = (int64_t{1} << (W - 1)) - 1;
    const int64_t SMin = -(int64_t{1} << (W - 1));
    const int64_t UMax = (int64_t{1} << W) - 1;

    const auto requireEquiv = [&](const char *Name, const camada::SMTExprRef &P,
                                  const camada::SMTExprRef &Ref) {
      INFO("width " << W << " " << Name);
      solver->addConstraint(solver->mkNot(solver->mkEqual(P, Ref)));
      REQUIRE(solver->check() == camada::CheckResult::UNSAT);
      solver->reset();
    };
    const auto symbols = [&]() {
      return std::make_pair(solver->mkSymbol("ovf_x", solver->mkBVSort(W)),
                            solver->mkSymbol("ovf_y", solver->mkBVSort(W)));
    };
    // Exact signed result at width W+n is out of [SMin, SMax].
    const auto signedOutOfRange = [&](const camada::SMTExprRef &Exact,
                                      unsigned Width) {
      return solver->mkOr(
          solver->mkBVSlt(Exact, solver->mkBVFromDec(SMin, Width)),
          solver->mkBVSgt(Exact, solver->mkBVFromDec(SMax, Width)));
    };
    // Exact unsigned result at width W+n exceeds UMax.
    const auto unsignedOutOfRange = [&](const camada::SMTExprRef &Exact,
                                        unsigned Width) {
      return solver->mkBVUgt(Exact, solver->mkBVFromDec(UMax, Width));
    };

    {
      auto [x, y] = symbols();
      auto Exact =
          solver->mkBVAdd(solver->mkBVSignExt(x, 1), solver->mkBVSignExt(y, 1));
      requireEquiv("saddo", solver->mkBVSAddOverflow(x, y),
                   signedOutOfRange(Exact, W + 1));
    }
    {
      auto [x, y] = symbols();
      auto Exact =
          solver->mkBVAdd(solver->mkBVZeroExt(x, 1), solver->mkBVZeroExt(y, 1));
      requireEquiv("uaddo", solver->mkBVUAddOverflow(x, y),
                   unsignedOutOfRange(Exact, W + 1));
    }
    {
      auto [x, y] = symbols();
      auto Exact =
          solver->mkBVSub(solver->mkBVSignExt(x, 1), solver->mkBVSignExt(y, 1));
      requireEquiv("ssubo", solver->mkBVSSubOverflow(x, y),
                   signedOutOfRange(Exact, W + 1));
    }
    {
      // The exact unsigned difference at W+1 bits is negative (top bit set)
      // iff the subtraction borrows.
      auto [x, y] = symbols();
      auto Exact =
          solver->mkBVSub(solver->mkBVZeroExt(x, 1), solver->mkBVZeroExt(y, 1));
      requireEquiv("usubo", solver->mkBVUSubOverflow(x, y),
                   solver->mkEqual(solver->mkBVExtract(W, W, Exact),
                                   solver->mkBVFromDec(1, 1)));
    }
    {
      auto [x, y] = symbols();
      auto Exact =
          solver->mkBVMul(solver->mkBVSignExt(x, W), solver->mkBVSignExt(y, W));
      requireEquiv("smulo", solver->mkBVSMulOverflow(x, y),
                   signedOutOfRange(Exact, 2 * W));
    }
    {
      auto [x, y] = symbols();
      auto Exact =
          solver->mkBVMul(solver->mkBVZeroExt(x, W), solver->mkBVZeroExt(y, W));
      requireEquiv("umulo", solver->mkBVUMulOverflow(x, y),
                   unsignedOutOfRange(Exact, 2 * W));
    }
    {
      // For a non-zero divisor the exact quotient at W+1 bits is out of
      // range only for MIN / -1. Division by zero is excluded explicitly:
      // it is never an overflow, but SMT-LIB defines bvsdiv(x<0, 0) = +1,
      // which falls outside [SMin, SMax] when W == 1.
      auto [x, y] = symbols();
      auto Exact = solver->mkBVSDiv(solver->mkBVSignExt(x, 1),
                                    solver->mkBVSignExt(y, 1));
      auto NonZeroY =
          solver->mkNot(solver->mkEqual(y, solver->mkBVFromDec(0, W)));
      requireEquiv("sdivo", solver->mkBVSDivOverflow(x, y),
                   solver->mkAnd(NonZeroY, signedOutOfRange(Exact, W + 1)));
    }
    {
      auto x = solver->mkSymbol("ovf_x", solver->mkBVSort(W));
      auto Exact = solver->mkBVNeg(solver->mkBVSignExt(x, 1));
      requireEquiv("nego", solver->mkBVNegOverflow(x),
                   signedOutOfRange(Exact, W + 1));
    }
  }
}

// Pins the narrow (width <= 64) decimal-constant path, which backends may
// serve through native integer APIs: negative values must produce the
// two's-complement pattern and values must be masked to the sort width.
inline void narrow_bv_decimal_model_value(const camada::SMTSolverRef &solver) {
  auto bv32 = solver->mkBVSort(32);
  auto x = solver->mkSymbol("x", bv32);
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(-42, bv32)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto bin = solver->getBVInBin(x);
  REQUIRE(bin);
  // -42 in 32-bit two's complement.
  REQUIRE(bin.value() == "11111111111111111111111111010110");

  solver->reset();
  auto bv3 = solver->mkBVSort(3);
  auto y = solver->mkSymbol("y", bv3);
  solver->addConstraint(solver->mkEqual(y, solver->mkBVFromDec(-1, bv3)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto bin3 = solver->getBVInBin(y);
  REQUIRE(bin3);
  REQUIRE(bin3.value() == "111");
}

// Pin model parsing for bit-vector widths above 64. Solvers that emit BV
// model values in the `(_ bv<n> <w>)` decimal form (mathsat is the canonical
// example over the SMT-LIB pipe) need an arbitrary-precision decimal-to-
// binary conversion; the previous 64-bit-cap implementation silently
// returned an empty result on widths >= 65.
inline void wide_bv_decimal_model_value(const camada::SMTSolverRef &solver) {
  auto bv128 = solver->mkBVSort(128);
  auto x = solver->mkSymbol("x", bv128);
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(42, bv128)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto bin = solver->getBVInBin(x);
  REQUIRE(bin);
  // 42 = 0b101010, zero-extended to 128 bits.
  std::string expected(128, '0');
  expected.replace(expected.size() - 6, 6, "101010");
  REQUIRE(bin.value() == expected);
}

inline void incremental_push_pop(const camada::SMTSolverRef &solver) {
  auto x = solver->mkSymbol("x", solver->mkBVSort(8));
  auto one = solver->mkBVFromDec(1, 8);
  auto two = solver->mkBVFromDec(2, 8);

  solver->addConstraint(solver->mkEqual(x, one));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  solver->push();
  solver->addConstraint(solver->mkEqual(x, two));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);

  solver->pop();
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  auto x_res = solver->getBV(x);
  REQUIRE(x_res);
  REQUIRE(x_res.value() == 1);
}

// Locks in the documented behavior that symbols are cached by (name, sort)
// for the solver's lifetime, including across push/pop. mkSymbol returns the
// same handle as before the push, even though SMT-LIB strict semantics would
// scope declarations to the popped frame. This matches every supported
// backend's actual C/C++ API behavior.
inline void symbol_cache_survives_push_pop(const camada::SMTSolverRef &solver) {
  auto bv8 = solver->mkBVSort(8);
  auto x_before = solver->mkSymbol("cached", bv8);
  REQUIRE(x_before.isValid());

  solver->push();
  REQUIRE(x_before.isValid());

  auto x_in_scope = solver->mkSymbol("cached", bv8);
  REQUIRE(x_in_scope.get() == x_before.get());

  solver->pop();
  REQUIRE(x_before.isValid());

  auto x_after = solver->mkSymbol("cached", bv8);
  REQUIRE(x_after.get() == x_before.get());

  // Confirm the cached symbol still participates in solving correctly after
  // the pop discarded the in-scope assertion.
  solver->addConstraint(solver->mkEqual(x_after, solver->mkBVFromDec(7, 8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  auto v = solver->getBV(x_before);
  REQUIRE(v);
  REQUIRE(v.value() == 7);
}

inline void
handle_invalidation_after_reset(const camada::SMTSolverRef &solver) {
#if !CAMADA_CHECKED_HANDLES
  // Unchecked handles are a raw pointer: reset cannot be detected and
  // stale use is undefined behavior by contract.
  (void)solver;
  SKIP("stale-handle detection is compiled out (CAMADA_CHECKED_HANDLES=OFF)");
#else
  auto sort = solver->mkBVSort(8);
  auto expr = solver->mkSymbol("stale", sort);

  REQUIRE(sort.isValid());
  REQUIRE(expr.isValid());

  solver->reset();

  REQUIRE_FALSE(sort.isValid());
  REQUIRE_FALSE(expr.isValid());

  auto fresh_sort = solver->mkBVSort(8);
  auto fresh_expr = solver->mkSymbol("fresh", fresh_sort);
  REQUIRE(fresh_sort.isValid());
  REQUIRE(fresh_expr.isValid());
#endif
}

// Pin the size contract ESBMC cares about: checked handles are pointer +
// state + generation; unchecked handles are exactly one pointer.
static_assert(sizeof(camada::SMTExprRef) == (CAMADA_CHECKED_HANDLES ? 24 : 8),
              "SMTExprRef size drifted from the documented layout");
static_assert(sizeof(camada::SMTSortRef) == (CAMADA_CHECKED_HANDLES ? 24 : 8),
              "SMTSortRef size drifted from the documented layout");

inline void quantifier_semantics(const camada::SMTSolverRef &solver) {
  auto x = solver->mkSymbol("x", solver->mkBVSort(4));
  solver->addConstraint(solver->mkForall({x}, solver->mkEqual(x, x)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  solver->reset();
  x = solver->mkSymbol("x", solver->mkBVSort(4));
  auto three = solver->mkBVFromDec(3, 4);
  solver->addConstraint(solver->mkExists({x}, solver->mkEqual(x, three)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  solver->reset();
  x = solver->mkSymbol("x", solver->mkBVSort(4));
  three = solver->mkBVFromDec(3, 4);
  solver->addConstraint(solver->mkForall({x}, solver->mkEqual(x, three)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
}

inline void uf_semantics(const camada::SMTSolverRef &solver) {
  auto bv4 = solver->mkBVSort(4);
  auto fsort = solver->mkFunctionSort({bv4}, bv4);
  auto f = solver->mkSymbol("f", fsort);
  auto x = solver->mkSymbol("x", bv4);
  auto y = solver->mkSymbol("y", bv4);
  auto fx = solver->mkApply(f, {x});
  auto fy = solver->mkApply(f, {y});
  REQUIRE(f->getKind() == camada::SMTExprKind::Symbol);
  REQUIRE(fx->getKind() == camada::SMTExprKind::Apply);
  REQUIRE(fy->getKind() == camada::SMTExprKind::Apply);

  solver->addConstraint(solver->mkEqual(x, y));
  solver->addConstraint(solver->mkNot(solver->mkEqual(fx, fy)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
}

inline void dump_string_semantics(const camada::SMTSolverRef &solver) {
  auto bv8 = solver->mkBVSort(8);
  auto x = solver->mkSymbol("x", bv8);
  auto five = solver->mkBVFromDec(5, 8);
  solver->addConstraint(solver->mkEqual(x, five));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  std::string sort_dump = "seed";
  bv8->dump(sort_dump);
  REQUIRE(!sort_dump.empty());
  REQUIRE(sort_dump != "seed");

  std::string expr_dump = "seed";
  x->dump(expr_dump);
  REQUIRE(!expr_dump.empty());
  REQUIRE(expr_dump != "seed");

  std::string solver_dump = "seed";
  solver->dump(solver_dump);
  REQUIRE(!solver_dump.empty());
  REQUIRE(solver_dump != "seed");

  std::string model_dump = "seed";
  solver->dumpModel(model_dump);
  REQUIRE(!model_dump.empty());
  REQUIRE(model_dump != "seed");

  // Regression: dumpModel with Camada-owned symbols in the symbol cache
  // (encoded tuples on backends without native datatypes carry no backend
  // term). Bitwuzla's model dump used to cast every cache entry to its
  // native expression type and SIGSEGV on the tuple node.
  solver->reset();
  auto tup = solver->mkSymbol(
      "dmt", solver->mkTupleSort({solver->mkBVSort(8), solver->mkBoolSort()}));
  solver->addConstraint(solver->mkEqual(solver->mkTupleSelect(tup, 0),
                                        solver->mkBVFromDec(7, 8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  std::string tuple_model_dump = "seed";
  solver->dumpModel(tuple_model_dump);
  REQUIRE(tuple_model_dump != "seed");
}

inline void int_arithmetic_semantics(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto x = solver->mkSymbol("x", int_sort);
  auto one = solver->mkInt(1);
  auto two = solver->mkInt(2);
  auto three = solver->mkInt(3);

  auto x_plus_one = solver->mkArithAdd(x, one);
  REQUIRE(x_plus_one->getKind() == camada::SMTExprKind::ArithAdd);

  solver->addConstraint(solver->mkEqual(x_plus_one, three));
  solver->addConstraint(solver->mkArithGt(x, two));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);

  solver->reset();
  int_sort = solver->mkIntSort();
  x = solver->mkSymbol("x", int_sort);
  one = solver->mkInt(1);
  two = solver->mkInt(2);
  three = solver->mkInt(3);
  x_plus_one = solver->mkArithAdd(x, one);
  solver->addConstraint(solver->mkEqual(x_plus_one, three));
  solver->addConstraint(solver->mkArithGt(x, one));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void bv_typed_getter_domain(const camada::SMTSolverRef &solver) {
  // getBV interprets the top bit as a sign, so its domain is exactly
  // int64_t: widths up to 64 signed, and anything wider (or an unsigned
  // value that does not fit) has to be reported rather than truncated.
  auto pin = [&](unsigned Width, const std::string &Bits) {
    auto x = solver->mkSymbol("g" + std::to_string(Width) + Bits,
                              solver->mkBVSort(Width));
    solver->addConstraint(solver->mkEqual(x, solver->mkBVFromBin(Bits)));
    REQUIRE(solver->check() == camada::CheckResult::SAT);
    return x;
  };

  // Width 64 with the top bit set: every such value used to come back as
  // -1, because the sign-extension mask shifted by the full width.
  {
    auto x = pin(64, "1" + std::string(63, '0'));
    auto v = solver->getBV(x);
    REQUIRE(v);
    REQUIRE(v.value() == INT64_MIN);
    auto u = solver->getBVUnsigned(x);
    REQUIRE(u);
    REQUIRE(u.value() == (1ULL << 63));
  }
  solver->reset();
  {
    auto x = pin(64, std::string(64, '1'));
    auto v = solver->getBV(x);
    REQUIRE(v);
    REQUIRE(v.value() == -1);
    auto u = solver->getBVUnsigned(x);
    REQUIRE(u);
    REQUIRE(u.value() == UINT64_MAX);
  }
  solver->reset();
  // A positive 64-bit value is unaffected, signed or unsigned.
  {
    auto x = pin(64, "0" + std::string(63, '1'));
    auto v = solver->getBV(x);
    REQUIRE(v);
    REQUIRE(v.value() == INT64_MAX);
    auto u = solver->getBVUnsigned(x);
    REQUIRE(u);
    REQUIRE(u.value() == static_cast<uint64_t>(INT64_MAX));
  }
  solver->reset();
  // Narrow widths keep working, both signs.
  {
    auto x = pin(8, "11111111");
    REQUIRE(solver->getBV(x).value() == -1);
    REQUIRE(solver->getBVUnsigned(x).value() == 255u);
  }
  solver->reset();
  // Wider than 64 bits fits in neither getter: report, do not truncate.
  {
    auto x = pin(72, std::string(72, '1'));
    auto v = solver->getBV(x);
    REQUIRE_FALSE(v);
    REQUIRE(v.error().Code == camada::SMTErrorCode::InvalidUsage);
    auto u = solver->getBVUnsigned(x);
    REQUIRE_FALSE(u);
    // getBVInBin stays the exact path for any width.
    auto bits = solver->getBVInBin(x);
    REQUIRE(bits);
    REQUIRE(bits.value() == std::string(72, '1'));
  }
}

// Every model getter is documented to return an SMTError, not abort, when
// no model is available. Before this was enforced in the common layer each
// backend failed its own way -- Z3 and cvc5 threw uncaught exceptions,
// Bitwuzla and MathSAT died, and STP fabricated an all-zeroes value, the
// worst outcome because the caller cannot tell it from a real answer.
inline void model_getters_require_a_model(const camada::SMTSolverRef &solver) {
  const auto requireNoModel = [&](const camada::SMTExprRef &E) {
    auto Bits = solver->getBVInBin(E);
    REQUIRE_FALSE(Bits);
    REQUIRE(Bits.error().Code == camada::SMTErrorCode::InvalidUsage);
  };

  auto x = solver->mkSymbol("nomodel_x", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(5, 8)));

  // No check has run yet. Every getter is gated, not just getBVInBin, so
  // sweep the sorts this fixture can build on every backend: a getter
  // added later without a guard fails here.
  requireNoModel(x);
  {
    const auto requireCode = [](const auto &Result) {
      REQUIRE_FALSE(Result);
      REQUIRE(Result.error().Code == camada::SMTErrorCode::InvalidUsage);
    };
    requireCode(solver->getBV(x));
    requireCode(solver->getBVUnsigned(x));
    requireCode(
        solver->getBool(solver->mkSymbol("nomodel_b", solver->mkBoolSort())));
    auto arr = solver->mkSymbol(
        "nomodel_arr",
        solver->mkArraySort(solver->mkBVSort(8), solver->mkBVSort(8)));
    requireCode(solver->getArrayElement(arr, solver->mkBVFromDec(0, 8)));
    requireCode(solver->getArrayValues(arr));
  }

  REQUIRE(solver->check() == camada::CheckResult::SAT);
  REQUIRE(solver->getBVInBin(x).value() == "00000101");

  // A scope change invalidates the model in both directions.
  solver->push();
  requireNoModel(x);
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  solver->pop();
  requireNoModel(x);

  // So does asserting.
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(6, 8)));
  requireNoModel(x);

  // UNSAT leaves no model to read.
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  requireNoModel(x);

  // checkSatAssuming leaves a readable model too. The default fallback
  // pops its assumption scope before returning, which clears the flag;
  // finishCheck() wraps the impl call, so the set always lands last.
  solver->reset();
  auto a = solver->mkSymbol("nomodel_a", solver->mkBoolSort());
  auto z = solver->mkSymbol("nomodel_z", solver->mkBVSort(8));
  solver->addConstraint(
      solver->mkImplies(a, solver->mkEqual(z, solver->mkBVFromDec(9, 8))));
  REQUIRE(solver->checkSatAssuming({a}) == camada::CheckResult::SAT);
  REQUIRE(solver->getBVInBin(z).value() == "00001001");

  // dumpModel reads the model like the getters do and must be gated the
  // same way: unguarded it aborted on Z3 and emitted fabricated text on
  // STP while the getter beside it correctly reported InvalidUsage.
  // It returns void, so writing nothing is the equivalent of SMTError.
  solver->reset();
  auto d = solver->mkSymbol("nomodel_d", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(d, solver->mkBVFromDec(3, 8)));
  {
    std::string Dump = "seed";
    solver->dumpModel(Dump);
    REQUIRE(Dump.empty());
  }
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  {
    // Non-emptiness alone is too weak: cvc5's dump evaluated each
    // *assertion* rather than each symbol, so it returned "true" under
    // SAT and satisfied that check while carrying no model at all. Require
    // the symbol to appear -- every backend names it, in its own syntax.
    std::string Dump;
    solver->dumpModel(Dump);
    REQUIRE(!Dump.empty());
    REQUIRE(Dump.find("nomodel_d") != std::string::npos);
  }

  // UNKNOWN is not a model. Most backends abort on a model query after
  // one (Z3 throws, Bitwuzla and Yices abort, MathSAT segfaults), so the
  // guard must reject it rather than pass it through. Skipped where the
  // limit is unenforceable, since then nothing produces an UNKNOWN.
  solver->reset();
  if (solver->setTimeout(150)) {
    // The limit survives reset() by design, and RESETANDTEST only resets, so
    // a REQUIRE failure below would leak 150ms into every later fixture and
    // bury this failure under unrelated UNKNOWNs. Clear it unconditionally.
    TimeoutGuard ClearTimeout{solver};
    auto p = assert_semiprime_factoring(solver, "nomodel");
    // A backend that ignores the limit and actually decides this is fine
    // -- then a model legitimately exists and the guard must allow it.
    if (solver->check() == camada::CheckResult::UNKNOWN)
      requireNoModel(p);
  }

  // And a reset clears it.
  solver->reset();
  auto y = solver->mkSymbol("nomodel_y", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(y, solver->mkBVFromDec(7, 8)));
  requireNoModel(y);
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  REQUIRE(solver->getBVInBin(y).value() == "00000111");
}

inline void pop_underflow_rejected(const camada::SMTSolverRef &solver) {
  // Popping past the root would take the backend below its own scope
  // floor while the common layer's journals stop at theirs, leaving the
  // two permanently out of step (Z3 threw "index out of bounds").
  solver->push(1);
  solver->pop(1);
  solver->push(2);
  solver->pop(2);
}

inline void null_sort_handle_equality(const camada::SMTSolverRef &solver) {
  // Sort handles are nullable, so comparison has to answer instead of
  // aborting inside the dereference.
  camada::SMTSortRef null_a, null_b;
  REQUIRE(null_a == null_b);
  REQUIRE_FALSE(null_a != null_b);

  auto live = solver->mkBVSort(8);
  REQUIRE(live != null_a);
  REQUIRE(null_a != live);
  REQUIRE_FALSE(live == null_a);

  // Two handles to the same sort still compare equal, and a different sort
  // still compares unequal -- the null check must not short-circuit those.
  REQUIRE(live == solver->mkBVSort(8));
  REQUIRE(live != solver->mkBVSort(16));
}

inline void
symbol_name_punctuation_distinct(const camada::SMTSolverRef &solver) {
  // Names differing only in punctuation are different symbols. A backend
  // that rewrites those characters to a common replacement aliases them,
  // which silently changes satisfiability: the conjunction below is
  // trivially satisfiable for distinct symbols and unsatisfiable if any
  // pair collapses into one variable. ESBMC generates all of these
  // (`main::1::x`, `x!0`, `&y`, `#tmp`).
  const char *Names[] = {"n@x", "n!x", "n&x", "n#x", "n$x", "n:x", "n_x"};
  auto sort = solver->mkBVSort(4);
  std::vector<camada::SMTExprRef> syms;
  for (const char *N : Names)
    syms.push_back(solver->mkSymbol(N, sort));

  // Pin each symbol to a distinct value. Seven names, sixteen values, so
  // this is satisfiable exactly when all seven are independent.
  for (std::size_t I = 0; I < syms.size(); ++I)
    solver->addConstraint(solver->mkEqual(
        syms[I], solver->mkBVFromDec(static_cast<int64_t>(I), 4)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  // And each really holds the value it was pinned to, so the names did not
  // merely survive but map to the right terms.
  for (std::size_t I = 0; I < syms.size(); ++I) {
    auto v = solver->getBV(syms[I]);
    REQUIRE(v);
    REQUIRE(v.value() == static_cast<int64_t>(I));
  }
}

inline void arith_division_semantics(const camada::SMTSolverRef &solver) {
  // Integer division truncates toward zero for positive operands and rounds
  // toward negative infinity for a negative dividend, per SMT-LIB `div`.
  // Real division is exact. A backend that routes Int operands through its
  // real-division operator answers 7/2 = 7/2 rather than 3, so pin both.
  auto int_sort = solver->mkIntSort();
  auto seven = solver->mkInt(7);
  auto two = solver->mkInt(2);
  auto q = solver->mkArithDiv(seven, two);
  REQUIRE(q->getKind() == camada::SMTExprKind::ArithDiv);
  REQUIRE(q->Sort->isIntSort());
  solver->addConstraint(solver->mkEqual(q, solver->mkInt(3)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  // 7/2 cannot also be 4: real division would make the equality above
  // unsatisfiable instead, so this pair fails either way if the operator
  // is wrong.
  solver->reset();
  solver->addConstraint(
      solver->mkEqual(solver->mkArithDiv(solver->mkInt(7), solver->mkInt(2)),
                      solver->mkInt(4)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);

  // SMT-LIB div floors: -7 div 2 = -4, not -3.
  solver->reset();
  solver->addConstraint(
      solver->mkEqual(solver->mkArithDiv(solver->mkInt(-7), solver->mkInt(2)),
                      solver->mkInt(-4)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  // A symbolic dividend, so the quotient is not constant-folded before it
  // reaches the backend operator. The divisor stays constant to keep the
  // formula linear -- some solvers reject symbolic division outright.
  solver->reset();
  int_sort = solver->mkIntSort();
  auto a = solver->mkSymbol("div_a", int_sort);
  solver->addConstraint(solver->mkEqual(a, solver->mkInt(9)));
  solver->addConstraint(solver->mkEqual(solver->mkArithDiv(a, solver->mkInt(4)),
                                        solver->mkInt(2)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  // Real division on the same numbers is exact: 9/4 is 2.25, not 2.
  solver->reset();
  auto real_sort = solver->mkRealSort();
  auto ra = solver->mkSymbol("div_ra", real_sort);
  solver->addConstraint(solver->mkEqual(ra, solver->mkReal(9)));
  auto rq = solver->mkArithDiv(ra, solver->mkReal(4));
  REQUIRE(rq->Sort->isRealSort());
  solver->addConstraint(solver->mkEqual(rq, solver->mkReal(2)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);

  solver->reset();
  real_sort = solver->mkRealSort();
  ra = solver->mkSymbol("div_ra", real_sort);
  solver->addConstraint(solver->mkEqual(ra, solver->mkReal(9)));
  solver->addConstraint(solver->mkEqual(
      solver->mkArithDiv(ra, solver->mkReal(4)), solver->mkReal("2.25")));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void real_arithmetic_semantics(const camada::SMTSolverRef &solver) {
  auto real_sort = solver->mkRealSort();
  auto r = solver->mkSymbol("r", real_sort);
  auto one = solver->mkReal(1);
  auto two = solver->mkReal(2);
  auto three = solver->mkReal(3);

  auto r_plus_one = solver->mkArithAdd(r, one);
  REQUIRE(r_plus_one->getKind() == camada::SMTExprKind::ArithAdd);

  solver->addConstraint(solver->mkEqual(r_plus_one, three));
  solver->addConstraint(solver->mkArithGt(r, one));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  solver->reset();
  real_sort = solver->mkRealSort();
  r = solver->mkSymbol("r", real_sort);
  one = solver->mkReal(1);
  two = solver->mkReal(2);
  three = solver->mkReal(3);
  (void)two;
  (void)three;
  solver->addConstraint(solver->mkEqual(r, one));
  solver->addConstraint(solver->mkArithLt(r, one));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
}

inline void arith_model_queries(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto real_sort = solver->mkRealSort();

  auto x = solver->mkSymbol("x", int_sort);
  auto r = solver->mkSymbol("r", real_sort);
  auto x_plus_two = solver->mkArithAdd(x, solver->mkInt("2"));
  auto r_plus_half = solver->mkArithAdd(r, solver->mkReal(1, 2));

  solver->addConstraint(solver->mkEqual(x, solver->mkInt(5)));
  solver->addConstraint(solver->mkEqual(r, solver->mkReal(3, 2)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto x_res = solver->getInt(x);
  auto x_plus_two_res = solver->getInt(x_plus_two);
  REQUIRE(x_res);
  REQUIRE(x_plus_two_res);
  REQUIRE(x_res.value() == "5");
  REQUIRE(x_plus_two_res.value() == "7");

  auto rational = solver->getRational(r);
  REQUIRE(rational);
  REQUIRE(rational.value().first == "3");
  REQUIRE(rational.value().second == "2");

  auto numerator = solver->getRealNumerator(r);
  auto denominator = solver->getRealDenominator(r);
  REQUIRE(numerator);
  REQUIRE(denominator);
  REQUIRE(numerator.value() == "3");
  REQUIRE(denominator.value() == "2");

  auto r_plus_half_res = solver->getInt(r_plus_half);
  REQUIRE(r_plus_half_res);
  REQUIRE(r_plus_half_res.value() == "2");
}

// Int <-> BV conversions (mkInt2BV / mkBV2Int): wrap semantics for
// negatives and out-of-range values, signed/unsigned interpretation,
// symbolic round trips, and the composition they exist for — bitwise
// operations on integers via convert / mkBV* / convert back.
inline void int_bv_conversion_semantics(const camada::SMTSolverRef &solver) {
  // int2bv wraps modulo 2^w: 300 -> 44 at 8 bits, -1 -> 0xFF.
  {
    auto bv = solver->mkInt2BV(solver->mkInt(300), 8);
    solver->addConstraint(solver->mkEqual(bv, solver->mkBVFromDec(44, 8)));
    REQUIRE(solver->check() == camada::CheckResult::SAT);
  }
  solver->reset();
  {
    auto bv = solver->mkInt2BV(solver->mkInt(-1), 8);
    solver->addConstraint(solver->mkEqual(bv, solver->mkBVFromDec(255, 8)));
    REQUIRE(solver->check() == camada::CheckResult::SAT);
  }

  // bv2int on 0xFF: 255 unsigned, -1 signed.
  solver->reset();
  {
    auto bv = solver->mkBVFromDec(255, 8);
    solver->addConstraint(
        solver->mkEqual(solver->mkBV2Int(bv, false), solver->mkInt(255)));
    solver->addConstraint(
        solver->mkEqual(solver->mkBV2Int(bv, true), solver->mkInt(-1)));
    REQUIRE(solver->check() == camada::CheckResult::SAT);
  }

  // Signed round trip is the identity on every in-range integer. The
  // universal (UNSAT) proofs run at 4 bits: the property is width-generic,
  // and on the fallback encoding (sum of bit-tests + Euclidean mod, used by
  // Yices and every SMT-LIB child) wider proofs made some children grind
  // for minutes.
  solver->reset();
  {
    auto x = solver->mkSymbol("i2b_x", solver->mkIntSort());
    solver->addConstraint(solver->mkArithGe(x, solver->mkInt(-8)));
    solver->addConstraint(solver->mkArithLe(x, solver->mkInt(7)));
    auto rt = solver->mkBV2Int(solver->mkInt2BV(x, 4), true);
    solver->addConstraint(solver->mkNot(solver->mkEqual(rt, x)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }

  // ... and the other way: int2bv(bv2int_u(y)) == y for every bit-vector.
  solver->reset();
  {
    auto y = solver->mkSymbol("i2b_y", solver->mkBVSort(4));
    auto rt = solver->mkInt2BV(solver->mkBV2Int(y, false), 4);
    solver->addConstraint(solver->mkNot(solver->mkEqual(rt, y)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }

  // The use case the bridge exists for: bitwise AND on integers
  // (12 & 10 == 8), computed as bv2int(bvand(int2bv, int2bv)).
  solver->reset();
  {
    auto r = solver->mkBV2Int(
        solver->mkBVAnd(solver->mkInt2BV(solver->mkInt(12), 8),
                        solver->mkInt2BV(solver->mkInt(10), 8)),
        true);
    solver->addConstraint(solver->mkEqual(r, solver->mkInt(8)));
    REQUIRE(solver->check() == camada::CheckResult::SAT);
  }

  // Signed composition: ~x == -x-1 must hold for all in-range x when
  // computed through the BV bridge.
  solver->reset();
  {
    auto x = solver->mkSymbol("i2b_x", solver->mkIntSort());
    solver->addConstraint(solver->mkArithGe(x, solver->mkInt(-8)));
    solver->addConstraint(solver->mkArithLe(x, solver->mkInt(7)));
    auto NotX = solver->mkBV2Int(solver->mkBVNot(solver->mkInt2BV(x, 4)), true);
    auto MinusXMinusOne =
        solver->mkArithSub(solver->mkArithNeg(x), solver->mkInt(1));
    solver->addConstraint(solver->mkNot(solver->mkEqual(NotX, MinusXMinusOne)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
}

inline void arith_conversion_semantics(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto real_sort = solver->mkRealSort();

  auto x = solver->mkSymbol("x", int_sort);
  auto r = solver->mkSymbol("r", real_sort);

  auto x_real = solver->mkInt2Real(x);
  auto r_int = solver->mkReal2Int(r);
  auto r_is_int = solver->mkIsInt(r);
  auto x_real_is_int = solver->mkIsInt(x_real);
  auto mod_expr = solver->mkArithMod(solver->mkInt("17"), solver->mkInt("5"));
  auto shl_expr = solver->mkArithShl(x, 3);

  REQUIRE(x_real->getKind() == camada::SMTExprKind::Int2Real);
  REQUIRE(r_int->getKind() == camada::SMTExprKind::Real2Int);
  REQUIRE(r_is_int->getKind() == camada::SMTExprKind::IsInt);
  REQUIRE(mod_expr->getKind() == camada::SMTExprKind::ArithMod);
  REQUIRE(shl_expr->getKind() == camada::SMTExprKind::ArithShl);

  solver->addConstraint(solver->mkEqual(x, solver->mkInt("5")));
  solver->addConstraint(solver->mkEqual(r, solver->mkReal(7, 2)));
  solver->addConstraint(solver->mkEqual(x_real, solver->mkReal("5")));
  solver->addConstraint(solver->mkEqual(r_int, solver->mkInt("3")));
  solver->addConstraint(solver->mkNot(r_is_int));
  solver->addConstraint(x_real_is_int);
  solver->addConstraint(solver->mkEqual(mod_expr, solver->mkInt("2")));
  solver->addConstraint(solver->mkEqual(shl_expr, solver->mkInt("40")));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void arith_symbolic_shift_semantics(const camada::SMTSolverRef &solver) {
  auto int_sort = solver->mkIntSort();
  auto x = solver->mkSymbol("x", int_sort);
  auto k = solver->mkSymbol("k", int_sort);
  auto shl_expr = solver->mkArithShl(x, k);

  REQUIRE(shl_expr->getKind() == camada::SMTExprKind::ArithShl);

  solver->addConstraint(solver->mkEqual(x, solver->mkInt("5")));
  solver->addConstraint(solver->mkEqual(k, solver->mkInt("3")));
  solver->addConstraint(solver->mkEqual(shl_expr, solver->mkInt("40")));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void arena_stress_test(const camada::SMTSolverRef &solver) {
  auto x = solver->mkSymbol("x", solver->mkBVSort(32));
  auto acc = x;

  // Force substantial arena growth with many distinct intermediate nodes.
  for (unsigned i = 0; i < 4096; ++i) {
    auto c0 = solver->mkBVFromDec(static_cast<int64_t>(i & 0xff), 32);
    auto c1 = solver->mkBVFromDec(static_cast<int64_t>((i * 3) & 0xff), 32);
    acc = solver->mkBVAdd(acc, c0);
    acc = solver->mkBVXor(acc, c1);
  }

  solver->addConstraint(solver->mkEqual(acc, acc));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  solver->reset();

  auto y = solver->mkSymbol("y", solver->mkBVSort(32));
  auto expr = y;
  for (unsigned i = 0; i < 2048; ++i) {
    auto c = solver->mkBVFromDec(static_cast<int64_t>((i + 7) & 0xff), 32);
    expr =
        solver->mkBVMul(solver->mkBVAdd(expr, c), solver->mkBVFromDec(3, 32));
  }

  solver->addConstraint(solver->mkEqual(expr, expr));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// Model query over a term with a shared subterm. On the SMT-LIB backend the
// (get-value ...) argument contains a let binding; child solvers must
// accept it and return the right value.
inline void shared_subterm_model_value(const camada::SMTSolverRef &solver) {
  auto bv8 = solver->mkBVSort(8);
  auto x = solver->mkSymbol("sst_x", bv8);
  auto sum = solver->mkBVAdd(x, x);
  auto prod = solver->mkBVMul(sum, sum);
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(3, bv8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto val = solver->getBV(prod);
  REQUIRE(val);
  REQUIRE(val.value() == 36);
}
