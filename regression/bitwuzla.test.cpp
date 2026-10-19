#include "matrix.test.h"
#include "tests.h"

// One test case per shared fixture group; capability gates and
// exclusions live in matrix.test.h.
CAMADA_SHARED_MATRIX(Bitwuzla, camada::createBitwuzlaSolver)

#include <catch2/catch_test_macros.hpp>
#include <cstring>
#include <random>
#include <solvers/bitwuzlasolver.h>

namespace {
// C++17: no designated initializers, so a tiny builder for the one field
// these tests flip.
inline camada::SolverConfig withUnsatAssumptions() {
  camada::SolverConfig Cfg;
  Cfg.UseUnsatAssumptions = true;
  return Cfg;
}
} // namespace

// Randomized cross-check of the BV-encoded fp.rem against the host CPU,
// which computes IEEE-754 remainder exactly. Full-bit-pattern inputs cover
// NaN/inf/subnormal operands; the seed is fixed for reproducibility.
TEST_CASE("FP remainder randomized host oracle Bitwuzla", "[Bitwuzla]") {
  auto solver = camada::createBitwuzlaSolver();

  // Raw mt19937 outputs are fully specified by the standard, so the sweep is
  // bit-identical across standard libraries.
  std::mt19937 Rng32(0xCA3ADAu);
  std::mt19937_64 Rng64(0xCA3ADAu);

  for (int I = 0; I < 200; ++I) {
    uint32_t XB = Rng32(), YB = Rng32();
    float X, Y;
    std::memcpy(&X, &XB, sizeof(X));
    std::memcpy(&Y, &YB, sizeof(Y));
    check_rem_pair_f32(solver, camada::FPEncoding::BV, X, Y);
  }

  for (int I = 0; I < 25; ++I) {
    uint64_t XB = Rng64(), YB = Rng64();
    double X, Y;
    std::memcpy(&X, &XB, sizeof(X));
    std::memcpy(&Y, &YB, sizeof(Y));
    check_rem_pair_f64(solver, camada::FPEncoding::BV, X, Y);
  }
}

TEST_CASE("Override Bitwuzla Solver", "[Bitwuzla]") {

  class myBitwuzlaSolver : public camada::BitwuzlaSolver {
  public:
    explicit myBitwuzlaSolver() { reset(); }

    void resetImpl() override {
      destroyContext();
      initializeContext();
    }
  };

  camada::SMTSolverRef bitwuzla = std::make_unique<myBitwuzlaSolver>();
  tests(bitwuzla);
}

// A subclass reaches the options before the instance exists, and again for
// every context a reset() builds.
TEST_CASE("Bitwuzla options hook survives reset", "[Bitwuzla]") {
  class optionsSolver : public camada::BitwuzlaSolver {
  public:
    explicit optionsSolver(bool Set) : Set(Set) {
      reset(); // the base constructor cannot reach the hook
    }

    unsigned Calls = 0;
    uint64_t preprocess() const {
      return bitwuzla_get_option(options(), BITWUZLA_OPT_PREPROCESS);
    }

  protected:
    void configureOptions(BitwuzlaOptions *Opts) override {
      ++Calls;
      if (Set)
        bitwuzla_set_option(Opts, BITWUZLA_OPT_PREPROCESS, 0);
    }

  private:
    bool Set;
  };

  optionsSolver solver(true);
  REQUIRE(solver.Calls == 1);
  REQUIRE(solver.preprocess() == 0);

  solver.reset();
  REQUIRE(solver.Calls == 2);
  REQUIRE(solver.preprocess() == 0);

  // Without the override the context keeps Bitwuzla's own setting.
  optionsSolver untouched(false);
  REQUIRE(untouched.preprocess() == 1);
}

TEST_CASE("Bitwuzla feature capabilities", "[Bitwuzla]") {
  auto solver = camada::createBitwuzlaSolver();
  using camada::SolverFeature;
  REQUIRE(solver->getSolverKind() == camada::SolverKind::Bitwuzla);
  REQUIRE_FALSE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE(solver->supports(SolverFeature::NativeRoundToAway));
  REQUIRE_FALSE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  // The capability is present either way; core extraction is opt-in at
  // construction because producing unsat assumptions slows every check,
  // so a default context reports the capability but leaves it disabled.
  REQUIRE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE_FALSE(solver->produceUnsatAssumptions());
  REQUIRE(solver->supports(SolverFeature::Timeouts));
  REQUIRE(solver->supports(SolverFeature::ArrayModels));

  auto withCores = camada::createBitwuzlaSolver(withUnsatAssumptions());
  REQUIRE(withCores->supports(SolverFeature::UnsatAssumptions));
  REQUIRE(withCores->produceUnsatAssumptions());
}

TEST_CASE("Unsat-assumption opt-in Bitwuzla test", "[Bitwuzla]") {
  // The default solver runs the shared fixture through its
  // core-unsupported branch (inside tests()); the opted-in solver must
  // produce real cores end to end.
  auto solver = camada::createBitwuzlaSolver(withUnsatAssumptions());
  check_sat_assuming_semantics(solver);
  // The shared fixture tolerates core-less backends, so pin explicitly
  // that this solver actually produces one — and that the opt-in survives
  // reset() (bitwuzla recreates its context there).
  solver->reset();
  REQUIRE(solver->supports(camada::SolverFeature::UnsatAssumptions));
  auto a = solver->mkSymbol("a", solver->mkBoolSort());
  REQUIRE(solver->checkSatAssuming({a, solver->mkNot(a)}) ==
          camada::CheckResult::UNSAT);
  auto core = solver->getUnsatAssumptions();
  REQUIRE(core);
  REQUIRE(!core.value().empty());
}
