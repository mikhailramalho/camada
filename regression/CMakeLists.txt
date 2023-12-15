include_directories(${CMAKE_SOURCE_DIR}/src)

set(REGRESSION_TARGET_NAME ${PROJECT_NAME}-regression)

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

find_package(Catch2 2 REQUIRED)

# add each solver specific implementation, if it is enabled
compile_test("Boolector;CVC5;MathSAT;STP;Yices;Z3")

add_executable(${REGRESSION_TARGET_NAME} main.cpp "${solver_test_files}")
target_link_libraries(${REGRESSION_TARGET_NAME} PRIVATE ${PROJECT_NAME} Catch2::Catch2)

# Solvers
if(${CAMADA_SOLVER_BOOLECTOR_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PRIVATE Boolector::boolector)
endif()

if(${CAMADA_SOLVER_CVC5_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC cvc5::cvc5)
endif()

if(${CAMADA_SOLVER_MATHSAT_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_MATHSAT_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_MATHSAT_INCLUDE_DIR})
endif()

if(${CAMADA_SOLVER_STP_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC stp)
endif()

if(${CAMADA_SOLVER_YICES_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_YICES_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_YICES_INCLUDE_DIR})
endif()

if(${CAMADA_SOLVER_Z3_ENABLE})
  target_link_libraries(${REGRESSION_TARGET_NAME} PUBLIC ${CAMADA_Z3_LIB})
  target_include_directories(${REGRESSION_TARGET_NAME}
                             PRIVATE ${CAMADA_Z3_INCLUDE_DIR})
endif()

include(Catch)
catch_discover_tests(${REGRESSION_TARGET_NAME})
