

#include "camada.h"
#include "simple.test.h"

#include <catch2/catch.hpp>
#include <yicessolver.h>

TEST_CASE("Simple yices test", "[YICES]") {
  // Create Yices Solver
  auto yices = camada::createYicesSolver();
  equal_ten(yices);
}
