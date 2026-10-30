// Smoke test for a Camada release: instantiate every backend the release
// shipped with, run a one-line SAT problem, and check that the model agrees.
// Built and run against the installed `camada::camada` package config in CI.

#include <camada/camada.h>
#include <camada/camadafeatures.h>

// Exercise the solvers/ include path too, so a broken install layout for
// the wrapper headers fails this consumer instead of a downstream build.
#if CAMADA_HAVE_Z3
#include <camada/solvers/z3solver.h>
#endif

#include <cstdint>
#include <iostream>
#include <string>

namespace {

int run(const camada::SMTSolverRef &solver, const std::string &name) {
  auto bv32 = solver->mkBVSort(32);
  auto x = solver->mkSymbol("x", bv32);
  auto seven = solver->mkBVFromDec(7, 32);
  solver->addConstraint(solver->mkEqual(x, seven));

  if (solver->check() != camada::CheckResult::SAT) {
    std::cerr << name << ": expected SAT\n";
    return 1;
  }

  auto value = solver->getBV(x);
  if (!value) {
    std::cerr << name << ": failed to read model: " << value.error().Message
              << "\n";
    return 1;
  }
  if (value.value() != static_cast<int64_t>(7)) {
    std::cerr << name << ": expected x = 7, got " << value.value() << "\n";
    return 1;
  }

  std::cout << name << ": ok\n";
  return 0;
}

} // namespace

int main() {
  int backends_exercised = 0;

#if CAMADA_HAVE_Z3
  if (run(camada::createZ3Solver(), "Z3") != 0)
    return 1;
  ++backends_exercised;

  // Z3 5.3 registers its tactics through static initializers. Linked from a
  // static archive the normal way, the linker drops the objects nothing else
  // pulls in and about a fifth of the tactics silently disappear, even in a
  // program that creates a solver. These are some of them.
  try {
    z3::context Ctx;
    for (const char *Name :
         {"ctx-solver-simplify", "elim-small-bv", "fm", "dt2bv", "eq2bv"})
      z3::tactic Tactic(Ctx, Name);
    std::cout << "Z3 tactics: ok\n";
  } catch (const z3::exception &E) {
    std::cerr << "Z3 tactics: " << E.msg() << "\n";
    return 1;
  }
#endif

#if CAMADA_HAVE_BITWUZLA
  if (run(camada::createBitwuzlaSolver(), "Bitwuzla") != 0)
    return 1;
  ++backends_exercised;
#endif

#if CAMADA_HAVE_CVC5
  if (run(camada::createCVC5Solver(), "CVC5") != 0)
    return 1;
  ++backends_exercised;
#endif

  if (backends_exercised == 0) {
    std::cerr << "release shipped with no backends the consumer test knows "
                 "how to drive\n";
    return 1;
  }
  return 0;
}
