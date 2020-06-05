include_directories(${CMAKE_BINARY_DIR}/src)

#-----------------------------------------------------------------------------#
# Macro to add solver files to test
function(compile_test)
  foreach(name IN LISTS ARGN)
    string(TOLOWER ${name} lower_name)

    if(CAMADA_ENABLE_SOLVER_${name})
      list(APPEND solver_src_test_files "${lower_name}.test.cpp")
    endif()

  set(solver_test_files ${solver_test_files} ${solver_src_test_files} PARENT_SCOPE)
  endforeach()
endfunction()

# add each solver specific implementation, if it is enabled
compile_test(${CAMADA_AVAILABLE_SOLVERS})

message("${solver_test_files}")

add_executable(camada-regression main.cpp "${solver_test_files}")

target_link_libraries(camada-regression
  PUBLIC camada Catch2::Catch2)

include(Catch)
catch_discover_tests(camada-regression)