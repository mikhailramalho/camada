function(add_header_to_install)
  foreach(name IN LISTS ARGN)
    string(TOLOWER ${name} lower_name)
    string(TOUPPER ${name} upper_name)

    if(CAMADA_SOLVER_${upper_name}_ENABLE AND ${name}_FOUND)
      list(APPEND solver_src_test_files "${lower_name}solver.h")
    endif()

    set(${LIBRARY_TARGET_NAME}_PUB_HDR
        ${${LIBRARY_TARGET_NAME}_PUB_HDR} ${solver_src_test_files}
        PARENT_SCOPE)
  endforeach()
endfunction()

# Include binary path so we can include ac_config.h
include_directories(${CMAKE_BINARY_DIR}/src)

# This is the "physical" (i.e. real) name of the library. The actual file name
# of the library built is constructed based on conventions of the native
# platform, such as lib<LIBRARY_TARGET_NAME>.a, lib<LIBRARY_TARGET_NAME>.dylib
# or <LIBRARY_TARGET_NAME>.lib.
set(LIBRARY_TARGET_NAME ${PROJECT_NAME})

# List of CPP (source) library files.
set(${LIBRARY_TARGET_NAME}_SRC
    camada.cpp
    camadaexpr.cpp
    camadasort.cpp
    camadaimpl.cpp
    boolectorsolver.cpp
    cvc4solver.cpp
    mathsatsolver.cpp
    stpsolver.cpp
    yicessolver.cpp
    z3solver.cpp)

# List of HPP (header) library files, the public ones will be installed on the
# system
set(${LIBRARY_TARGET_NAME}_PUB_HDR camada.h camadasort.h camadaexpr.h
                                   camadaimpl.h)

# add each solver specific header, if it is enabled
add_header_to_install("Boolector;CVC4;MathSAT;STP;Yices;Z3")

set(${LIBRARY_TARGET_NAME}_HDR camadaimpl.h)

# Adds a library target called ${LIBRARY_TARGET_NAME} to be built from the
# source and header files listed in the command invocation.
add_library(
  ${LIBRARY_TARGET_NAME}
  ${${LIBRARY_TARGET_NAME}_SRC} ${${LIBRARY_TARGET_NAME}_HDR}
  ${${LIBRARY_TARGET_NAME}_PUB_HDR})

# Within this project, you can link to this library by just specifing the name
# of the target, i.e. ${LIBRARY_TARGET_NAME} = LibTemplateCMake. It is useful,
# however, to define an alias of this library with the scope of the exported
# library itself because (1) you will link against it with the exact same syntax
# of an imported library and (2) because names having a double-colon (::) are
# always treated as the name of either an alias or imported target. Any attempt
# to use such a name for a different target type will result in an error.
add_library(${PROJECT_NAME}::${LIBRARY_TARGET_NAME} ALIAS
            ${LIBRARY_TARGET_NAME})

# Solvers
if(${CAMADA_SOLVER_BOOLECTOR_ENABLE})
  target_link_libraries(${LIBRARY_TARGET_NAME} PUBLIC Boolector::boolector)
  target_compile_definitions(${LIBRARY_TARGET_NAME}
                             PRIVATE SOLVER_BOOLECTOR_ENABLED)
endif()

if(${CAMADA_SOLVER_CVC4_ENABLE})
  target_link_libraries(${LIBRARY_TARGET_NAME} PUBLIC CVC4::cvc4)
  target_compile_definitions(${LIBRARY_TARGET_NAME} PRIVATE SOLVER_CVC4_ENABLED)
  if(DEFINED CAMADA_CVC4_SYMFPU_DIR)
    target_include_directories(${LIBRARY_TARGET_NAME}
                               PRIVATE ${CAMADA_CVC4_SYMFPU_DIR})
  endif()
endif()

if(${CAMADA_SOLVER_MATHSAT_ENABLE})
  target_link_libraries(${LIBRARY_TARGET_NAME} PUBLIC ${CAMADA_MATHSAT_LIB})
  target_include_directories(${LIBRARY_TARGET_NAME}
                             PRIVATE ${CAMADA_MATHSAT_INCLUDE_DIR})
  target_compile_definitions(${LIBRARY_TARGET_NAME}
                             PRIVATE SOLVER_MATHSAT_ENABLED)
endif()

if(${CAMADA_SOLVER_STP_ENABLE})
  target_link_libraries(${LIBRARY_TARGET_NAME} PUBLIC ${CAMADA_STP_LIB})
  target_include_directories(${LIBRARY_TARGET_NAME}
                             PRIVATE ${CAMADA_STP_INCLUDE_DIR})
  target_compile_definitions(${LIBRARY_TARGET_NAME} PRIVATE SOLVER_STP_ENABLED)
endif()

if(${CAMADA_SOLVER_YICES_ENABLE})
  target_link_libraries(${LIBRARY_TARGET_NAME} PUBLIC ${CAMADA_YICES_LIB})
  target_include_directories(${LIBRARY_TARGET_NAME}
                             PRIVATE ${CAMADA_YICES_INCLUDE_DIR})
  target_compile_definitions(${LIBRARY_TARGET_NAME}
                             PRIVATE SOLVER_YICES_ENABLED)
endif()

if(${CAMADA_SOLVER_Z3_ENABLE})
  target_link_libraries(${LIBRARY_TARGET_NAME} PUBLIC ${CAMADA_Z3_LIB})
  target_include_directories(${LIBRARY_TARGET_NAME}
                             PRIVATE ${CAMADA_Z3_INCLUDE_DIR})
  target_compile_definitions(${LIBRARY_TARGET_NAME} PRIVATE SOLVER_Z3_ENABLED)
endif()

# Set two minimum target properties for the library. See
# https://cmake.org/cmake/help/latest/command/set_target_properties.html
# Properties are: 1) Library version number 2) list of corresponding public
# headers
set_target_properties(
  ${LIBRARY_TARGET_NAME}
  PROPERTIES VERSION ${${PROJECT_NAME}_VERSION}
             PUBLIC_HEADER "${${LIBRARY_TARGET_NAME}_PUB_HDR}")

# Specify include directories for both compilation and installation process. The
# $<INSTALL_PREFIX> generator expression is useful to ensure to create
# relocatable configuration files, see
# https://cmake.org/cmake/help/latest/manual/cmake-packages.7.html#creating-relocatable-packages
target_include_directories(
  ${LIBRARY_TARGET_NAME}
  PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
         "$<INSTALL_INTERFACE:$<INSTALL_PREFIX>/${CMAKE_INSTALL_INCLUDEDIR}>")

if(${RELEASE_MODE})
  add_custom_target(
    repack-btor-static-lib ALL
    COMMAND
      rm -rf btor && mkdir btor && cd btor &&
      ar -x "../../../deps/install/lib/libboolector.a" && cd ../ &&
      rm -rf ling && mkdir ling && cd ling &&
      ar -x "../../../deps/src/boolector-3.2.1/deps/lingeling/liblgl.a" &&  cd ../ &&
      rm -rf btor2tool && mkdir btor2tool && cd btor2tool &&
      ar -x "../../../deps/src/boolector-3.2.1/deps/btor2tools/build/libbtor2parser.a" && cd ../ &&
      rm -rf mini && mkdir mini && cd mini &&
      ar -x "../../../deps/install/lib/libminisat.a" && cd ../ &&
      rm -rf cms && mkdir cms && cd cms &&
      ar -x "../../../deps/install/lib/libcryptominisat5.a" &&  cd ../ &&
      rm -rf cad && mkdir cad && cd cad &&
      ar -x "../../../deps/install/lib/libcadical.a" && cd ../ &&
      rm -rf z3 && mkdir z3 && cd z3 &&
      ar -x "../../../deps/install/bin/libz3.a" && cd ../ &&
      rm -rf stp && mkdir stp && cd stp &&
      ar -x "../../../deps/install/lib/libstp.a" && cd ../ &&
      rm -rf main && mkdir main && cd main &&
      ar -x "../../lib/$<TARGET_FILE_NAME:${LIBRARY_TARGET_NAME}>" && cd ../ &&
      ar -qc "../lib/$<TARGET_FILE_NAME:${LIBRARY_TARGET_NAME}>" ./*/*.o)
endif()

# Specify installation targets, typology and destination folders.
install(
  TARGETS ${LIBRARY_TARGET_NAME}
  EXPORT ${PROJECT_NAME}
  LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}" COMPONENT shlib
  ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}" COMPONENT lib
  RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}" COMPONENT bin
  PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/${LIBRARY_TARGET_NAME}"
                COMPONENT dev)
