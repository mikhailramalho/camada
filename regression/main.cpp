#include <catch2/catch_session.hpp>

int main(int argc, char *argv[]) {
  Catch::Session session;
  return session.run(argc, argv);
}

#include "camada.h"

#include <catch2/catch_test_macros.hpp>

// Pins the configure-time substitution in scripts/cmake/cmake_config.in:
// a quoting mistake there once shipped the literal macro names as the
// version string, and nothing noticed.
TEST_CASE("Camada version string", "[Camada]") {
  REQUIRE(camada::getCamadaVersion() == "0.11");
}
