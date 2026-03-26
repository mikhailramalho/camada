
#include "tests.h"

#include <bitwuzlasolver.h>
#include <catch2/catch_test_macros.hpp>

TEST_CASE("Simple Bitwuzla test", "[Bitwuzla]") {
  auto bitwuzla = camada::createBitwuzlaSolver();
  tests(bitwuzla);
}

TEST_CASE("Quantifiers Bitwuzla test", "[Bitwuzla]") {
  auto bitwuzla = camada::createBitwuzlaSolver();
  quantifier_semantics(bitwuzla);
}

TEST_CASE("Override Bitwuzla Solver", "[Bitwuzla]") {

  class myBitwuzlaSolver : public camada::BitwuzlaSolver {
  public:
    explicit myBitwuzlaSolver() { resetImpl(); }

    void resetImpl() override {
      SymbolTable.clear();
      destroyContext();
      initializeContext();
    }
  };

  camada::SMTSolverRef bitwuzla = std::make_unique<myBitwuzlaSolver>();
  tests(bitwuzla);
}
