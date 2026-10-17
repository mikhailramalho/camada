#include "tests.h"
#include "matrix.test.h"

// One test case per shared fixture group; capability gates and
// exclusions live in matrix.test.h.
CAMADA_SHARED_MATRIX(Z3, camada::createZ3Solver)

#include <catch2/catch_test_macros.hpp>
#include <solvers/z3solver.h>

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
  if (solver->check() == camada::CheckResult::UNKNOWN)
    REQUIRE(solver->reasonUnknown() == camada::UnknownReason::BackendError);
}
