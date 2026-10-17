#include "matrix.test.h"
#include "tests.h"

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

// CVC5's native constant array takes only a value. Auto routes a symbolic
// initializer to the lazy lowering (const_array_nonliteral_initializer proves
// that works); an explicit Native request is rejected rather than quietly
// answered with a different term.
TEST_CASE("CVC5 native constant arrays reject a non-literal initializer",
          "[CVC5]") {
  auto solver = camada::createCVC5Solver();
  auto idx = solver->mkBVSort(3);
  auto elem = solver->mkBVSort(8);
  auto sym = solver->mkSymbol("init_sym", elem);

  require_abort([&]() {
    (void)solver->mkArrayConst(idx, sym, camada::ConstArrayLowering::Native);
  });

  // A literal is still native, and Auto still builds the symbolic one.
  auto literal = solver->mkBVFromDec(5, elem);
  REQUIRE(solver->mkArrayConst(idx, literal, camada::ConstArrayLowering::Native)
              ->getKind() == camada::SMTExprKind::ArrayConst);
  auto lazy = solver->mkArrayConst(idx, sym);
  REQUIRE(lazy->isArraySort());

  // A tuple literal is a value too.
  auto tuple = solver->mkTuple({literal, solver->mkBool(true)});
  REQUIRE(solver->mkArrayConst(idx, tuple, camada::ConstArrayLowering::Native)
              ->getKind() == camada::SMTExprKind::ArrayConst);
}
