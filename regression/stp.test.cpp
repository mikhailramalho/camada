
#include "tests.h"

#include <catch2/catch_test_macros.hpp>
#include <stpsolver.h>

TEST_CASE("Simple STP test", "[STP]") {
  // Create STP Solver
  auto stp = camada::createSTPSolver();
  tests(stp);
}

TEST_CASE("Unsupported UF STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto bv4 = stp->mkBVSort(4);
    auto fn = stp->mkFunctionSort({bv4}, bv4);
    (void)stp->mkSymbol("f", fn);
  });
}

TEST_CASE("Small constant array STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  auto idx = stp->mkBVSort(4);
  auto elem = stp->mkBVFromDec(7, 8);
  auto arr = stp->mkArrayConst(idx, elem);
  auto sel = stp->getArrayElement(arr, stp->mkBVFromDec(3, 4));
  auto sel_res = stp->getBV(sel);
  REQUIRE(sel_res);
  REQUIRE(sel_res.value() == 7);
}

// Large index widths used to abort (the old lowering emitted one store per
// index); the lazy constant-array lowering handles any width.
TEST_CASE("Large-width constant array STP test", "[STP]") {
  auto stp = camada::createSTPSolver();
  lazy_const_array_semantics(stp);
}
