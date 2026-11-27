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

// get_value on a term over a quantifier Bitwuzla never registered returns the
// term itself. getArrayValues used to read that as an empty model with no
// base, which says every index is unconstrained.
TEST_CASE("Bitwuzla array model over an unasserted quantifier", "[Bitwuzla]") {
  auto solver = camada::createBitwuzlaSolver();
  auto bv8 = solver->mkBVSort(8);
  auto arr = solver->mkArraySort(bv8, bv8);
  auto x = solver->mkSymbol("x", bv8);
  auto y = solver->mkSymbol("y", bv8);
  auto a = solver->mkSymbol("a", arr);
  auto c = solver->mkSymbol("c", arr);
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(0, bv8)));
  solver->addConstraint(solver->mkNot(solver->mkEqual(a, c)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto q = solver->mkForall({y}, solver->mkBVUle(x, y));
  auto av = solver->getArrayValues(solver->mkIte(q, a, c));
  REQUIRE(!av);
  REQUIRE(av.error().Code == camada::SMTErrorCode::InvalidModelValue);

  // An ordinary array still reads normally.
  auto ok = solver->getArrayValues(a);
  REQUIRE(ok);
  REQUIRE(ok.value().Base);
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
  REQUIRE(solver->supports(SolverFeature::Renew));

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

// Bitwuzla's model is partial: get_value on a term over a quantifier it never
// registered returns the term itself, and the value getters aborted on it.
TEST_CASE("Bitwuzla model values over an unasserted quantifier", "[Bitwuzla]") {
  auto solver = camada::createBitwuzlaSolver();
  auto bv8 = solver->mkBVSort(8);
  auto x = solver->mkSymbol("x", bv8);
  auto y = solver->mkSymbol("y", bv8);
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(0, bv8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto q = solver->mkForall({y}, solver->mkBVUle(x, y));
  auto b = solver->getBool(q);
  REQUIRE(!b);
  REQUIRE(b.error().Code == camada::SMTErrorCode::InvalidModelValue);

  auto bv = solver->getBVInBin(solver->mkIte(q, x, y));
  REQUIRE(!bv);
  REQUIRE(bv.error().Code == camada::SMTErrorCode::InvalidModelValue);

  auto fp = solver->getFPInBin(
      solver->mkIte(q, solver->mkFP32(1.0f, camada::FPEncoding::Native),
                    solver->mkFP32(2.0f, camada::FPEncoding::Native)));
  REQUIRE(!fp);
  REQUIRE(fp.error().Code == camada::SMTErrorCode::InvalidModelValue);

  // An ordinary term still reads normally.
  REQUIRE(solver->getBVUnsigned(x).value() == 0);
}

TEST_CASE("Bitwuzla renew keeps terms and starts empty", "[Bitwuzla]") {
  auto solver = camada::createBitwuzlaSolver();
  auto bv8 = solver->mkBVSort(8);
  auto x = solver->mkSymbol("x", bv8);
  auto y = solver->mkSymbol("y", bv8);
  auto xIs5 = solver->mkEqual(x, solver->mkBVFromDec(5, bv8));
  solver->addConstraint(xIs5);
  solver->push();
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(6, bv8)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);

  // From inside a scope: the new instance is at scope 0 with nothing
  // asserted, and the model is gone.
  solver->renew();
  REQUIRE_FALSE(solver->getBVUnsigned(x));
  solver->push();
  solver->addConstraint(solver->mkEqual(x, solver->mkBVFromDec(7, bv8)));
  REQUIRE(solver->check() == camada::CheckResult::SAT); // x == 5 is gone
  solver->pop();

  // Every handle made before renew() still works, and builds new terms.
  solver->addConstraint(xIs5);
  solver->addConstraint(
      solver->mkEqual(y, solver->mkBVAdd(x, solver->mkBVFromDec(1, bv8))));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  REQUIRE(solver->getBVUnsigned(x).value() == 5);
  REQUIRE(solver->getBVUnsigned(y).value() == 6);
  solver->push();
  solver->addConstraint(solver->mkEqual(y, x));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  solver->pop();
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// Ackermann reads are tied by congruence axioms only camada asserts, so
// renew() has to assert them on the new instance, including those made
// inside a scope that was open at the time.
TEST_CASE("Bitwuzla renew asserts camada's own facts again", "[Bitwuzla]") {
  camada::SolverConfig Cfg;
  Cfg.Arrays = camada::ArrayEncoding::Ackermann;
  auto solver = camada::createBitwuzlaSolver(Cfg);
  auto bv8 = solver->mkBVSort(8);
  auto a = solver->mkSymbol("a", solver->mkArraySort(bv8, bv8));
  auto i = solver->mkSymbol("i", bv8);
  auto j = solver->mkSymbol("j", bv8);
  auto ri = solver->mkArraySelect(a, i);
  solver->push();
  auto rj = solver->mkArraySelect(a, j);

  solver->renew();
  solver->addConstraint(solver->mkEqual(i, j));
  solver->addConstraint(solver->mkNot(solver->mkEqual(ri, rj)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
}

// Asserting x == to_fp(bits) at scope 0 makes mkIEEEFPToBV(x) return bits.
// That rewrite relies on the equality, so renew() asserts it again even
// though the caller does not.
TEST_CASE("Bitwuzla renew keeps the equalities behind fp-to-bits shadows",
          "[Bitwuzla]") {
  auto solver = camada::createBitwuzlaSolver();
  auto fp32 = solver->mkFP32Sort(camada::FPEncoding::Native);
  auto x = solver->mkSymbol("x", fp32);
  auto bits = solver->mkSymbol("bits", solver->mkBVSort(32));
  solver->addConstraint(solver->mkEqual(x, solver->mkBVToIEEEFP(bits, fp32)));
  auto xBits = solver->mkIEEEFPToBV(x);

  solver->renew();
  solver->addConstraint(
      solver->mkFPEqual(x, solver->mkFP32(1.0f, camada::FPEncoding::Native)));
  // The bits of 2.0f.
  solver->addConstraint(
      solver->mkEqual(xBits, solver->mkBVFromDec(0x40000000, 32)));
  REQUIRE(solver->check() == camada::CheckResult::UNSAT);
}

// Only the equality that made the shadow is kept: a second equality for the
// same term is the caller's alone and does not survive renew().
TEST_CASE("Bitwuzla renew keeps only the equality behind a shadow",
          "[Bitwuzla]") {
  auto solver = camada::createBitwuzlaSolver();
  auto fp32 = solver->mkFP32Sort(camada::FPEncoding::Native);
  auto bv32 = solver->mkBVSort(32);
  auto x = solver->mkSymbol("x", fp32);
  auto b1 = solver->mkSymbol("b1", bv32);
  auto b2 = solver->mkSymbol("b2", bv32);
  auto e1 = solver->mkEqual(x, solver->mkBVToIEEEFP(b1, fp32));
  auto e2 = solver->mkEqual(x, solver->mkBVToIEEEFP(b2, fp32));
  solver->addConstraint(e1);
  solver->addConstraint(e2);

  solver->renew();
  solver->addConstraint(
      solver->mkEqual(b1, solver->mkBVFromDec(0x3f800000, 32)));
  solver->addConstraint(
      solver->mkEqual(b2, solver->mkBVFromDec(0x40000000, 32)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}
