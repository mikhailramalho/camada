include_directories(${CMAKE_BINARY_DIR}/src)

#-----------------------------------------------------------------------------#
# Macro to add solver files to test
function(compile_test)
  foreach(name IN LISTS ARGN)
    string(TOLOWER ${name} lower_name)

    if(CAMADA_ENABLE_SOLVER_${name})
      set(test_src_files "${test_src_files}" "${lower_name}.test.cpp" PARENT_SCOPE)
    endif()
  endforeach()
endfunction()

# Add base test
set(test_src_files main.cpp)

# And add each solver specific implementation, if it is enabled
compile_test(${CAMADA_AVAILABLE_SOLVERS})

add_executable(camada-regression ${test_src_files})

target_link_libraries(camada-regression
  PUBLIC camada Catch2::Catch2)

include(Catch)
catch_discover_tests(camada-regression)