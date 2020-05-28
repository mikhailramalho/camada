include_directories(${CMAKE_CURRENT_BINARY_DIR})

set(libcamada_src_files camada.cpp z3solver.cpp)

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
