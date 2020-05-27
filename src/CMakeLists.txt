include_directories(${CMAKE_CURRENT_BINARY_DIR})

set(libcamada_src_files version.cpp)

set(libcamada_headers_files version.h)

if(BUILD_SHARED_LIBS)
  add_library(camada SHARED ${libcamada_src_files})
  target_link_libraries(camada ${LIBRARIES})

  install(TARGETS camada
    EXPORT camada-export
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
  )

  install(FILES ${libcamada_headers_files} DESTINATION include)
endif()

if(BUILD_STATIC_LIBS)
  add_library(camada-static STATIC ${libcamada_src_files})
  target_link_libraries(camada ${LIBRARIES})

  install(TARGETS camada-static
    EXPORT camada-export
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
  )

  install(FILES ${libcamada_headers_files} DESTINATION include)

  if(NOT WIN32)
    set_target_properties(camada-static PROPERTIES OUTPUT_NAME camada)
  endif()
endif()
