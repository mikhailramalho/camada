
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

TEST_CASE("Large-width constant array STP aborts cleanly", "[STP]") {
  auto stp = camada::createSTPSolver();
  require_abort([&]() {
    auto idx = stp->mkBVSort(64);
    auto elem = stp->mkBVFromDec(1, 8);
    (void)stp->mkArrayConst(idx, elem);
  });
}
