#include "tests.h"
#include "matrix.test.h"

// One test case per shared fixture group; capability gates and
// exclusions live in matrix.test.h.
CAMADA_SHARED_MATRIX(CVC5, camada::createCVC5Solver)

#include <catch2/catch_test_macros.hpp>
#include <solvers/cvc5solver.h>

namespace {
// C++17: no designated initializers, so a tiny builder for the one field
// these tests flip.
inline camada::SolverConfig withUnsatAssumptions() {
  camada::SolverConfig Cfg;
  Cfg.UseUnsatAssumptions = true;
  return Cfg;
}
} // namespace

TEST_CASE("CVC5 feature capabilities", "[CVC5]") {
  auto solver = camada::createCVC5Solver();
  using camada::SolverFeature;
  REQUIRE(solver->getSolverKind() == camada::SolverKind::CVC5);
  REQUIRE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE(solver->supports(SolverFeature::NativeRoundToAway));
  REQUIRE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  // The capability is present either way; core extraction is opt-in at
  // construction because producing unsat assumptions slows every check,
  // so a default context reports the capability but leaves it disabled.
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE_FALSE(solver->produceUnsatAssumptions());
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE(solver->supports(SolverFeature::ArrayModels));

  auto withCores = camada::createCVC5Solver(withUnsatAssumptions());
  REQUIRE(withCores->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(withCores->produceUnsatAssumptions());
}

TEST_CASE("Unsat-assumption opt-in CVC5 test", "[CVC5]") {
  // The default solver runs the shared fixture through its
  // core-unsupported branch (inside tests()); the opted-in solver must
  // produce real cores end to end.
  auto solver = camada::createCVC5Solver(withUnsatAssumptions());
  check_sat_assuming_semantics(solver);
  // The shared fixture tolerates core-less backends, so pin explicitly
  // that this solver actually produces one — and that the opt-in survives
  // reset() (cvc5 keeps its options through resetAssertions()).
  solver->reset();
  REQUIRE(solver->supports(camada::SolverFeature::UnsatAssumptions));
  auto a = solver->mkSymbol("a", solver->mkBoolSort());
  REQUIRE(solver->checkSatAssuming({a, solver->mkNot(a)}) ==
          camada::CheckResult::UNSAT);
  auto core = solver->getUnsatAssumptions();
  REQUIRE(core);
  REQUIRE(!core.value().empty());
}
