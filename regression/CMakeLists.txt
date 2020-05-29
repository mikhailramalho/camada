add_executable(camada-regression
  z3.test.cpp
)

target_link_libraries(camada-regression
  PUBLIC camada Catch2::Catch2)

include(Catch)
catch_discover_tests(camada-regression)