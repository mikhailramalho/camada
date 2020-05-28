include_directories(${CMAKE_CURRENT_BINARY_DIR})

set(libcamada_src_files camada.cpp z3solver.cpp)
set(libcamada_headers_files camada.h)

add_library(camada ${libcamada_src_files})
target_link_libraries(camada fmt::fmt ${CAMADA_SOLVER_LIBS})

install(TARGETS camada
  EXPORT camada-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(FILES ${libcamada_headers_files} DESTINATION include)
