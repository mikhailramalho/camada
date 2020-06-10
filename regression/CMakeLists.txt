include_directories(${CMAKE_SOURCE_DIR}/src)

#-----------------------------------------------------------------------------#
# Macro to add solver files to test
function(compile_test)
  foreach(name IN LISTS ARGN)
    string(TOLOWER ${name} lower_name)

    if(CAMADA_ENABLE_SOLVER_${name})
      if(NOT EXISTS "${CMAKE_SOURCE_DIR}/regression/${lower_name}.test.cpp")
        message(FATAL_ERROR "Could not find regression file ${CMAKE_SOURCE_DIR}/regression/${lower_name}.test.cpp")
      endif()
      list(APPEND solver_src_test_files "${lower_name}.test.cpp")
    endif()

  set(solver_test_files ${solver_src_test_files} PARENT_SCOPE)
  endforeach()
endfunction()

# add each solver specific implementation, if it is enabled
compile_test(${CAMADA_AVAILABLE_SOLVERS})

add_executable(camada-regression main.cpp "${solver_test_files}")

target_link_libraries(camada-regression camada Catch2::Catch2 ${CAMADA_SOLVER_LIBS})

include(Catch)
catch_discover_tests(camada-regression)