include_directories(${CMAKE_BINARY_DIR}/src)

#-----------------------------------------------------------------------------#
# Macro to add solver files to compile
function(compile_solver)
  foreach(name IN LISTS ARGN)
    string(TOLOWER ${name} lower_name)

    if(CAMADA_ENABLE_SOLVER_${name})
      set(libcamada_src_files "${libcamada_src_files}" "${lower_name}solver.cpp" PARENT_SCOPE)
    endif()
  endforeach()
endfunction()

# Add base implementation
set(libcamada_src_files camada.cpp)

# And compile each solver specific implementation, if it is enabled
compile_solver(${CAMADA_AVAILABLE_SOLVERS})

add_library(camada ${libcamada_src_files})
target_link_libraries(camada fmt::fmt ${CAMADA_SOLVER_LIBS})

target_include_directories(camada INTERFACE ./)

install(TARGETS camada
  EXPORT camada-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

#-----------------------------------------------------------------------------#
# Macro to add solver header to install
function(install_solver_header)
  foreach(name IN LISTS ARGN)
    string(TOLOWER ${name} lower_name)

    if(CAMADA_ENABLE_SOLVER_${name})
      install(FILES "${lower_name}solver.h" DESTINATION include)
    endif()
  endforeach()
endfunction()

# Install camada header
install(FILES camada.h DESTINATION include)

# And header for each enabled solver
install_solver_header(${CAMADA_AVAILABLE_SOLVERS})
