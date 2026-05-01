// Smoke test for a Camada release: instantiate every backend the release
// shipped with, run a one-line SAT problem, and check that the model agrees.
// Built and run against the installed `camada::camada` package config in CI.

#include <camada/camada.h>
#include <camada/camadafeatures.h>

#include <cstdint>
#include <iostream>
#include <string>

namespace {

int run(const camada::SMTSolverRef &solver, const std::string &name) {
  auto bv32 = solver->mkBVSort(32);
  auto x = solver->mkSymbol("x", bv32);
  auto seven = solver->mkBVFromDec(7, 32);
  solver->addConstraint(solver->mkEqual(x, seven));

  if (solver->check() != camada::checkResult::SAT) {
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
#endif

#if CAMADA_HAVE_BITWUZLA
  if (run(camada::createBitwuzlaSolver(), "Bitwuzla") != 0)
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
