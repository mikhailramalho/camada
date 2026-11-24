// Built with NDEBUG, whatever the library was built with. The installed
// headers must give SMTSort the same layout either way: a client whose NDEBUG
// differed from the library's used to read a WidthValidated field the library
// never wrote (#357).
#include "camada.h"

#include <catch2/catch_test_macros.hpp>

#ifndef NDEBUG
#error "ndebug.test.cpp must be compiled with NDEBUG"
#endif

#if CAMADA_HAVE_Z3
TEST_CASE("Sort layout does not depend on NDEBUG", "[Z3]") {
  auto solver = camada::createZ3Solver();
  REQUIRE(solver->mkBVSort(8)->isWidthValidated());
  REQUIRE(solver->mkBoolSort()->isWidthValidated());
}
#endif
