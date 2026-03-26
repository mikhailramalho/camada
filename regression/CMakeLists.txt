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

add_executable(${REGRESSION_TARGET_NAME} main.cpp "${solver_test_files}")
target_link_libraries(${REGRESSION_TARGET_NAME} PRIVATE ${PROJECT_NAME}
                                                        Catch2::Catch2)

add_executable(${BENCH_TARGET_NAME} bench/main.cpp)
target_link_libraries(${BENCH_TARGET_NAME} PRIVATE ${PROJECT_NAME})

# Solvers
if(${CAMADA_SOLVER_BITWUZLA_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PRIVATE PkgConfig::Bitwuzla)
  target_compile_definitions(${BENCH_TARGET_NAME}
                             PRIVATE SOLVER_BITWUZLA_ENABLED)
endif()

if(${CAMADA_SOLVER_CVC5_ENABLE})
  target_link_directories(
    ${REGRESSION_TARGET_NAME} PRIVATE ${CAMADA_DEPS_INSTALL_DIR}/lib
    ${CAMADA_DEPS_INSTALL_DIR}/lib64)
  target_link_directories(
    ${BENCH_TARGET_NAME} PRIVATE ${CAMADA_DEPS_INSTALL_DIR}/lib
    ${CAMADA_DEPS_INSTALL_DIR}/lib64)
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC cvc5::cvc5)
  if(CAMADA_CVC5_EXTRA_LIBS)
    target_link_libraries(${REGRESSION_TARGET_NAME}
                          PUBLIC ${CAMADA_CVC5_EXTRA_LIBS})
    target_link_libraries(${BENCH_TARGET_NAME} PUBLIC ${CAMADA_CVC5_EXTRA_LIBS})
  endif()
  target_compile_definitions(${BENCH_TARGET_NAME} PRIVATE SOLVER_CVC5_ENABLED)
endif()

if(${CAMADA_SOLVER_MATHSAT_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_MATHSAT_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_MATHSAT_INCLUDE_DIR})
  target_compile_definitions(${BENCH_TARGET_NAME}
                             PRIVATE SOLVER_MATHSAT_ENABLED)
endif()

if(${CAMADA_SOLVER_STP_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC stp)
  target_compile_definitions(${BENCH_TARGET_NAME} PRIVATE SOLVER_STP_ENABLED)
endif()

if(${CAMADA_SOLVER_YICES_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_YICES_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_YICES_INCLUDE_DIR})
  target_compile_definitions(${BENCH_TARGET_NAME} PRIVATE SOLVER_YICES_ENABLED)
endif()

if(${CAMADA_SOLVER_Z3_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_Z3_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_Z3_INCLUDE_DIR})
  target_compile_definitions(${BENCH_TARGET_NAME} PRIVATE SOLVER_Z3_ENABLED)
  get_filename_component(CAMADA_Z3_LIB_DIR "${CAMADA_Z3_LIB}" DIRECTORY)
  if(EXISTS "${CAMADA_Z3_LIB_DIR}")
    target_link_directories(${REGRESSION_TARGET_NAME} PRIVATE
                            ${CAMADA_Z3_LIB_DIR})
    target_link_directories(${BENCH_TARGET_NAME} PRIVATE ${CAMADA_Z3_LIB_DIR})
    set_property(
      TARGET ${REGRESSION_TARGET_NAME}
      APPEND
      PROPERTY BUILD_RPATH "${CAMADA_Z3_LIB_DIR}")
    set_property(
      TARGET ${BENCH_TARGET_NAME}
      APPEND
      PROPERTY BUILD_RPATH "${CAMADA_Z3_LIB_DIR}")
  endif()
endif()

include(Catch)
catch_discover_tests(${REGRESSION_TARGET_NAME})
