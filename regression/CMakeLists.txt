include_directories(${CMAKE_SOURCE_DIR}/src)
include_directories(${CMAKE_BINARY_DIR}/src)

set(REGRESSION_TARGET_NAME ${PROJECT_NAME}-regression)
set(BENCH_TARGET_NAME ${PROJECT_NAME}-bench)

# -----------------------------------------------------------------------------#
# Macro to add solver files to test
function(compile_test)
  foreach(name IN LISTS ARGN)
    string(TOLOWER ${name} lower_name)
    string(TOUPPER ${name} upper_name)

    if(CAMADA_SOLVER_${upper_name}_ENABLE AND ${name}_FOUND)
      if(NOT EXISTS "${CMAKE_SOURCE_DIR}/regression/${lower_name}.test.cpp")
        message(
          FATAL_ERROR
            "Could not find regression file ${CMAKE_SOURCE_DIR}/regression/${lower_name}.test.cpp"
        )
      endif()
      list(APPEND solver_src_test_files "${lower_name}.test.cpp")
    endif()

    set(solver_test_files
        ${solver_src_test_files}
        PARENT_SCOPE)
  endforeach()
endfunction()

if(NOT TARGET Catch2::Catch2)
  find_package(Catch2 3 REQUIRED)
endif()
if(DEFINED Catch2_SOURCE_DIR)
  list(APPEND CMAKE_MODULE_PATH "${Catch2_SOURCE_DIR}/extras")
endif()

# add each solver specific implementation, if it is enabled
compile_test("Bitwuzla;CVC5;MathSAT;STP;Yices;Z3")

set(REGRESSION_SOURCES main.cpp "${solver_test_files}")
if(CAMADA_SOLVER_SMTLIB_ENABLE)
  list(APPEND REGRESSION_SOURCES smtlib.test.cpp)
endif()
add_executable(${REGRESSION_TARGET_NAME} ${REGRESSION_SOURCES})
target_link_libraries(${REGRESSION_TARGET_NAME} PRIVATE ${PROJECT_NAME}
                                                        Catch2::Catch2)

# Hints for the SMT-LIB pipeline tests: prefer locally-staged solver binaries if
# Camada's dependency download produced them. The pipeline tests are
# parameterized over every binary that's actually on disk, falling back to PATH
# for missing ones. Each macro is defined only when the binary is present; the
# test code uses #ifdef to discover them.
if(EXISTS "${CAMADA_DEPS_INSTALL_DIR}/bin/z3")
  target_compile_definitions(
    ${REGRESSION_TARGET_NAME}
    PRIVATE "CAMADA_TEST_Z3_BIN=\"${CAMADA_DEPS_INSTALL_DIR}/bin/z3\"")
endif()
if(EXISTS "${CAMADA_DEPS_INSTALL_DIR}/bin/cvc5")
  target_compile_definitions(
    ${REGRESSION_TARGET_NAME}
    PRIVATE "CAMADA_TEST_CVC5_BIN=\"${CAMADA_DEPS_INSTALL_DIR}/bin/cvc5\"")
endif()
if(EXISTS "${CAMADA_DEPS_INSTALL_DIR}/bin/bitwuzla")
  target_compile_definitions(
    ${REGRESSION_TARGET_NAME}
    PRIVATE
      "CAMADA_TEST_BITWUZLA_BIN=\"${CAMADA_DEPS_INSTALL_DIR}/bin/bitwuzla\"")
endif()
if(EXISTS "${CAMADA_DEPS_INSTALL_DIR}/bin/yices-smt2")
  target_compile_definitions(
    ${REGRESSION_TARGET_NAME}
    PRIVATE
      "CAMADA_TEST_YICES_SMT2_BIN=\"${CAMADA_DEPS_INSTALL_DIR}/bin/yices-smt2\""
  )
endif()

# MathSAT ships a binary inside its vendor archive. On macOS the vendor binary
# hard-codes /opt/local/lib/libgmp.10.dylib; CamadaDependencies.cmake copies it
# into ${CAMADA_DEPS_INSTALL_DIR}/bin and rewrites the load path so it can run
# without MacPorts, so prefer that staged copy. Fall back to globbing the
# unpacked source tree (Linux, or macOS hosts where staging was skipped).
# CONFIGURE_DEPENDS makes CMake re-evaluate the glob on every build so a dep
# version bump (e.g. 5.6.15 -> 5.6.16) is picked up without manually re-running
# `cmake -S . -B build`.
set(CAMADA_MATHSAT_BIN_PATH "")
if(EXISTS "${CAMADA_DEPS_INSTALL_DIR}/bin/mathsat")
  set(CAMADA_MATHSAT_BIN_PATH "${CAMADA_DEPS_INSTALL_DIR}/bin/mathsat")
else()
  file(GLOB CAMADA_MATHSAT_BIN_CANDIDATES CONFIGURE_DEPENDS
       "${CAMADA_DEPS_SRC_DIR}/mathsat-*/bin/mathsat")
  if(CAMADA_MATHSAT_BIN_CANDIDATES)
    list(GET CAMADA_MATHSAT_BIN_CANDIDATES 0 CAMADA_MATHSAT_BIN_PATH)
  endif()
endif()
if(CAMADA_MATHSAT_BIN_PATH)
  target_compile_definitions(
    ${REGRESSION_TARGET_NAME}
    PRIVATE "CAMADA_TEST_MATHSAT_BIN=\"${CAMADA_MATHSAT_BIN_PATH}\"")
endif()

# The bench driver reads /proc/self/statm and is Linux-shaped; we only measure
# performance on Linux. Skip the target on Windows entirely.
if(NOT WIN32)
  add_executable(${BENCH_TARGET_NAME} bench/main.cpp)
  target_link_libraries(${BENCH_TARGET_NAME} PRIVATE ${PROJECT_NAME})
endif()

# Solvers
if(${CAMADA_SOLVER_BITWUZLA_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PRIVATE PkgConfig::Bitwuzla)
  if(TARGET ${BENCH_TARGET_NAME})
    target_compile_definitions(${BENCH_TARGET_NAME}
                               PRIVATE SOLVER_BITWUZLA_ENABLED)
  endif()
endif()

if(${CAMADA_SOLVER_CVC5_ENABLE})
  target_link_directories(
    ${REGRESSION_TARGET_NAME} PRIVATE ${CAMADA_DEPS_INSTALL_DIR}/lib
    ${CAMADA_DEPS_INSTALL_DIR}/lib64)
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC cvc5::cvc5)
  if(CAMADA_CVC5_EXTRA_LIBS)
    target_link_libraries(${REGRESSION_TARGET_NAME}
                          PUBLIC ${CAMADA_CVC5_EXTRA_LIBS})
  endif()
  if(TARGET ${BENCH_TARGET_NAME})
    target_link_directories(
      ${BENCH_TARGET_NAME} PRIVATE ${CAMADA_DEPS_INSTALL_DIR}/lib
      ${CAMADA_DEPS_INSTALL_DIR}/lib64)
    if(CAMADA_CVC5_EXTRA_LIBS)
      target_link_libraries(${BENCH_TARGET_NAME}
                            PUBLIC ${CAMADA_CVC5_EXTRA_LIBS})
    endif()
    target_compile_definitions(${BENCH_TARGET_NAME} PRIVATE SOLVER_CVC5_ENABLED)
  endif()
endif()

if(${CAMADA_SOLVER_MATHSAT_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_MATHSAT_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_MATHSAT_INCLUDE_DIR})
  if(TARGET ${BENCH_TARGET_NAME})
    target_compile_definitions(${BENCH_TARGET_NAME}
                               PRIVATE SOLVER_MATHSAT_ENABLED)
  endif()
endif()

if(${CAMADA_SOLVER_STP_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC stp)
  if(TARGET ${BENCH_TARGET_NAME})
    target_compile_definitions(${BENCH_TARGET_NAME} PRIVATE SOLVER_STP_ENABLED)
  endif()
endif()

if(${CAMADA_SOLVER_YICES_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_YICES_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_YICES_INCLUDE_DIR})
  if(TARGET ${BENCH_TARGET_NAME})
    target_compile_definitions(${BENCH_TARGET_NAME}
                               PRIVATE SOLVER_YICES_ENABLED)
  endif()
endif()

if(CAMADA_SOLVER_SMTLIB_ENABLE)
  target_compile_definitions(${REGRESSION_TARGET_NAME}
                             PRIVATE SOLVER_SMTLIB_ENABLED)
endif()

if(${CAMADA_SOLVER_Z3_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_Z3_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_Z3_INCLUDE_DIR})
  # Tell the regression sources whether Z3 was compiled in. Per-backend test
  # files (z3.test.cpp etc.) are only included in the build when their backend
  # is enabled, so they don't need this guard, but cross-backend tests
  # (smtlib.test.cpp) do.
  target_compile_definitions(${REGRESSION_TARGET_NAME}
                             PRIVATE SOLVER_Z3_ENABLED)
  if(TARGET ${BENCH_TARGET_NAME})
    target_compile_definitions(${BENCH_TARGET_NAME} PRIVATE SOLVER_Z3_ENABLED)
  endif()
  get_filename_component(CAMADA_Z3_LIB_DIR "${CAMADA_Z3_LIB}" DIRECTORY)
  if(EXISTS "${CAMADA_Z3_LIB_DIR}")
    target_link_directories(${REGRESSION_TARGET_NAME} PRIVATE
                            ${CAMADA_Z3_LIB_DIR})
    set_property(
      TARGET ${REGRESSION_TARGET_NAME}
      APPEND
      PROPERTY BUILD_RPATH "${CAMADA_Z3_LIB_DIR}")
    if(TARGET ${BENCH_TARGET_NAME})
      target_link_directories(${BENCH_TARGET_NAME} PRIVATE ${CAMADA_Z3_LIB_DIR})
      set_property(
        TARGET ${BENCH_TARGET_NAME}
        APPEND
        PROPERTY BUILD_RPATH "${CAMADA_Z3_LIB_DIR}")
    endif()
  endif()
endif()

include(Catch)
catch_discover_tests(${REGRESSION_TARGET_NAME})
