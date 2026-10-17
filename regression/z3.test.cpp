#include "matrix.test.h"
#include "tests.h"

// One test case per shared fixture group; capability gates and
// exclusions live in matrix.test.h.
CAMADA_SHARED_MATRIX(Z3, camada::createZ3Solver)

#include <catch2/catch_test_macros.hpp>
#include <solvers/z3solver.h>
#include <stdexcept>

// The fixed<->float oracle tables bit-blast thousands of FP circuits, so
// unlike the other FXP fixtures they run on one backend instead of all
// seven. The conversions are pure common-layer encoding over BV ops that
// every backend already exercises, and the encoding-sensitive cases are
// pinned per backend by fxp_fp_conversion_semantics inside tests().
// Every input of both 16-bit _Accum formats through mkFXPExp. Each exp is
// a wide multiply chain, so this costs ~130s and runs on one backend
// rather than all seven; the encoding is common-layer BV, so the other
// backends' spot checks in tests() are enough.
TEST_CASE("Fixed-point exp exhaustive Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  fxp_exp_exhaustive(z3);
}

TEST_CASE("Fixed-point/floating-point oracle Z3 test", "[Z3]") {
  auto z3 = camada::createZ3Solver();
  fxp_oracle_fp_semantics(z3, camada::FPEncoding::BV);
}

// The full shared fixture suite under the Ackermann encoding — the same
// coverage the native-array mode gets, so every composition (const
// arrays, tuples, FP, FXP, push/pop, models) is proven against the
// encoding, not just the targeted ack_* fixtures.
TEST_CASE("Ackermann full fixture suite Z3 test", "[Z3]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto z3 = camada::createZ3Solver(Cfg);
  tests(z3);
}

TEST_CASE("Ackermann arrays reject quantifiers Z3 test", "[Z3]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto z3 = camada::createZ3Solver(Cfg);
  require_abort([&]() {
    auto x = z3->mkSymbol("x", z3->mkBVSort(4));
    (void)z3->mkForall({x}, z3->mkEqual(x, x));
  });
}

TEST_CASE("Override Z3 Solver", "[Z3]") {

  class myZ3Solver : public camada::Z3Solver {
  public:
    explicit myZ3Solver(z3::config &Cfg) : camada::Z3Solver(Cfg) {
      setSolver(makeSolver(context()));
    }

  private:
    static z3::solver makeSolver(z3::context &C) {
      return (z3::tactic(C, "simplify") & z3::tactic(C, "solve-eqs") &
              z3::tactic(C, "simplify") & z3::tactic(C, "smt"))
          .mk_solver();
    }
  };

  // Create Z3 Solver from a caller-owned configuration; the context is
  // built inside the solver (z3::context cannot be moved in Z3 4.13.x).
  z3::config Cfg;
  camada::SMTSolverRef z3 = std::make_unique<myZ3Solver>(Cfg);

  tests(z3);
}

TEST_CASE("Z3 feature capabilities", "[Z3]") {
  auto solver = camada::createZ3Solver();
  using camada::SolverFeature;
  REQUIRE(solver->getSolverKind() == camada::SolverKind::Z3);
  REQUIRE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE(solver->supports(SolverFeature::NativeRoundToAway));
  REQUIRE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE(solver->supports(SolverFeature::ArrayModels));
}

// Z3 4.13 throws from check() on this query once a scope is open; camada
// reports that as UNKNOWN. A fixed Z3 may decide it, so only an UNKNOWN is
// checked.
TEST_CASE("Z3 internal exceptions surface as UNKNOWN", "[Z3]") {
  auto solver = camada::createZ3Solver();
  solver->push();
  auto b = solver->mkSymbol("b", solver->mkBVSort(1));
  auto f = solver->mkSBVToFP(
      b, solver->mkFP32Sort(camada::FPEncoding::Native),
      solver->mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::Native));
  solver->addConstraint(
      solver->mkFPLt(f, solver->mkFP32(0.0f, camada::FPEncoding::Native)));
  if (solver->check() == camada::CheckResult::UNKNOWN) {
    REQUIRE(solver->reasonUnknown() == camada::UnknownReason::BackendError);
    // The exception's own text is kept, not swallowed.
    REQUIRE_FALSE(solver->reasonUnknownDetail().empty());
  }
}

// A backend exception out of a check is caught once, in the core, on every
// check path: check(), checkSatAssuming() and its push/check/pop fallback.
TEST_CASE("Backend exceptions from a check surface as UNKNOWN", "[Z3]") {
  class ThrowingZ3 : public camada::Z3Solver {
  public:
    explicit ThrowingZ3(z3::config &Cfg) : camada::Z3Solver(Cfg) {}
    bool Throw = true;

  protected:
    camada::CheckResult checkImpl() override {
      if (Throw)
        throw std::runtime_error("boom");
      return camada::Z3Solver::checkImpl();
    }
    camada::CheckResult
    checkSatAssumingImpl(const std::vector<camada::SMTExprRef> &A) override {
      return camada::SMTSolverImpl::checkSatAssumingImpl(A);
    }
  };

  z3::config Cfg;
  auto Owned = std::make_unique<ThrowingZ3>(Cfg);
  ThrowingZ3 &Throwing = *Owned;
  camada::SMTSolverRef solver = std::move(Owned);
  auto b = solver->mkSymbol("b", solver->mkBoolSort());

  auto expectBoom = [&](camada::CheckResult R) {
    REQUIRE(R == camada::CheckResult::UNKNOWN);
    REQUIRE(solver->reasonUnknown() == camada::UnknownReason::BackendError);
    REQUIRE(solver->reasonUnknownDetail() == "boom");
  };
  expectBoom(solver->check());
  expectBoom(solver->checkSatAssuming({}));
  expectBoom(solver->checkSatAssuming({b}));

  // The fallback popped its scope on the way out; the solver still works.
  Throwing.Throw = false;
  solver->addConstraint(solver->mkNot(b));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  REQUIRE(solver->checkSatAssuming({b}) == camada::CheckResult::UNSAT);
}

// The detail travels with the reason and dies with it. Z3 5.3 no longer throws
// on the query above, so a backend that fails on demand pins the plumbing.
TEST_CASE("Unknown-reason detail follows the reason", "[Z3]") {
  class FailingZ3 : public camada::Z3Solver {
  public:
    explicit FailingZ3(z3::config &Cfg) : camada::Z3Solver(Cfg) {}
    bool Fail = true;

  protected:
    camada::CheckResult checkImpl() override {
      if (!Fail)
        return camada::Z3Solver::checkImpl();
      noteUnknownReason(camada::UnknownReason::BackendError, "boom");
      return camada::CheckResult::UNKNOWN;
    }
  };

  z3::config Cfg;
  auto Owned = std::make_unique<FailingZ3>(Cfg);
  FailingZ3 &Failing = *Owned;
  camada::SMTSolverRef solver = std::move(Owned);

  // Nothing has failed yet.
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::NotApplicable);
  REQUIRE(solver->reasonUnknownDetail().empty());

  REQUIRE(solver->check() == camada::CheckResult::UNKNOWN);
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::BackendError);
  REQUIRE(solver->reasonUnknownDetail() == "boom");

  // A later check that answers clears both.
  Failing.Fail = false;
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::NotApplicable);
  REQUIRE(solver->reasonUnknownDetail().empty());

  // So does a reset, which discards the query the reason belonged to.
  Failing.Fail = true;
  REQUIRE(solver->check() == camada::CheckResult::UNKNOWN);
  REQUIRE(solver->reasonUnknownDetail() == "boom");
  solver->reset();
  REQUIRE(solver->reasonUnknown() == camada::UnknownReason::NotApplicable);
  REQUIRE(solver->reasonUnknownDetail().empty());
}
