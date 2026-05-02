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
    camadafp.cpp
    camadaimpl.cpp
    camadasort.cpp
    camadatuple.cpp
    bitwuzlasolver.cpp
    cvc5solver.cpp
    mathsatsolver.cpp
    stpsolver.cpp
    yicessolver.cpp
    z3solver.cpp)

if(CAMADA_SOLVER_SMTLIB_ENABLE)
  list(APPEND ${LIBRARY_TARGET_NAME}_SRC smtlibsolver.cpp)
endif()

# List of HPP (header) library files, the public ones will be installed on the
# system
set(${LIBRARY_TARGET_NAME}_PUB_HDR
    camada.h
    camadaarena.h
    camadacache.h
    camadacommon.h
    camadaexpr.h
    camadahandle.h
    camadaimpl.h
    camadasort.h)

if(CAMADA_SOLVER_SMTLIB_ENABLE)
  list(APPEND ${LIBRARY_TARGET_NAME}_PUB_HDR smtlibsolver.h)
endif()

# add each solver specific header, if it is enabled
add_header_to_install("Bitwuzla;CVC5;MathSAT;STP;Yices;Z3")

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
#
# The installed <backend>solver.h headers `#include` the backend's own headers
# (z3++.h, bitwuzla/c/bitwuzla.h, etc.), so consumers compiling against Camada
# must see the same headers Camada itself was built with. Propagate the
# bundled-backend include path PUBLIC and wrap it in BUILD_INTERFACE because the
# bundled solvers are not staged into Camada's install prefix — installed
# consumers must supply their own backend headers. If a consumer also has a
# system copy of the same backend (/opt/homebrew/include, /usr/local/include) on
# its own -I list, they must arrange for Camada's propagated -I to come first;
# this CMake side only ensures the path reaches the consumer at all.
#
# Collect the per-backend PUBLIC link libraries into a single list so we can
# wrap them in LINK_GROUP RESCAN for static builds on linkers that need it. With
# BUILD_SHARED_LIBS=OFF, the GNU linker resolves symbols left-to-right in a
# single pass; backend archives reference each other (e.g. libyices.a →
# libgmp.a, libcvc5.a → libcadical.a) and produce undefined references when one
# comes before the archive that defines its symbols. RESCAN tells the linker to
# iterate over the listed archives until the symbol set converges (--start-group
# / --end-group on GNU ld / lld / mold). LINK_GROUP requires the backend libs to
# be passed as a single generator-expression argument, hence the up-front
# collection.
set(_camada_backend_link_libs "")

if(${CAMADA_SOLVER_BITWUZLA_ENABLE})
  list(APPEND _camada_backend_link_libs ${Bitwuzla_LINK_LIBRARIES})
  target_include_directories(
    ${LIBRARY_TARGET_NAME} PUBLIC "$<BUILD_INTERFACE:${Bitwuzla_INCLUDE_DIRS}>")
  target_compile_definitions(${LIBRARY_TARGET_NAME}
                             PRIVATE SOLVER_BITWUZLA_ENABLED)
endif()

if(${CAMADA_SOLVER_CVC5_ENABLE})
  target_link_directories(
    ${LIBRARY_TARGET_NAME} PRIVATE ${CAMADA_DEPS_INSTALL_DIR}/lib
    ${CAMADA_DEPS_INSTALL_DIR}/lib64)
  list(APPEND _camada_backend_link_libs cvc5::cvc5)
  if(CAMADA_CVC5_EXTRA_LIBS)
    list(APPEND _camada_backend_link_libs ${CAMADA_CVC5_EXTRA_LIBS})
  endif()
  target_compile_definitions(${LIBRARY_TARGET_NAME} PRIVATE SOLVER_CVC5_ENABLED)
endif()

if(${CAMADA_SOLVER_MATHSAT_ENABLE})
  list(APPEND _camada_backend_link_libs ${CAMADA_MATHSAT_LIB})
  target_include_directories(
    ${LIBRARY_TARGET_NAME}
    PUBLIC "$<BUILD_INTERFACE:${CAMADA_MATHSAT_INCLUDE_DIR}>")
  target_compile_definitions(${LIBRARY_TARGET_NAME}
                             PRIVATE SOLVER_MATHSAT_ENABLED)
endif()

if(${CAMADA_SOLVER_STP_ENABLE})
  list(APPEND _camada_backend_link_libs stp)
  target_include_directories(${LIBRARY_TARGET_NAME}
                             PUBLIC "$<BUILD_INTERFACE:${STP_INCLUDE_DIRS}>")
  target_compile_definitions(${LIBRARY_TARGET_NAME} PRIVATE SOLVER_STP_ENABLED)
endif()

if(${CAMADA_SOLVER_YICES_ENABLE})
  list(APPEND _camada_backend_link_libs ${CAMADA_YICES_LIB})
  target_include_directories(
    ${LIBRARY_TARGET_NAME}
    PUBLIC "$<BUILD_INTERFACE:${CAMADA_YICES_INCLUDE_DIR}>")
  target_compile_definitions(${LIBRARY_TARGET_NAME}
                             PRIVATE SOLVER_YICES_ENABLED)
endif()

if(${CAMADA_SOLVER_Z3_ENABLE})
  list(APPEND _camada_backend_link_libs ${CAMADA_Z3_LIB})
  target_include_directories(
    ${LIBRARY_TARGET_NAME} PUBLIC "$<BUILD_INTERFACE:${CAMADA_Z3_INCLUDE_DIR}>")
  get_filename_component(CAMADA_Z3_LIB_DIR "${CAMADA_Z3_LIB}" DIRECTORY)
  if(BUILD_SHARED_LIBS AND EXISTS "${CAMADA_Z3_LIB_DIR}")
    target_link_directories(${LIBRARY_TARGET_NAME} PRIVATE ${CAMADA_Z3_LIB_DIR})
    set_property(
      TARGET ${LIBRARY_TARGET_NAME}
      APPEND
      PROPERTY BUILD_RPATH "${CAMADA_Z3_LIB_DIR}")
  endif()
  target_compile_definitions(${LIBRARY_TARGET_NAME} PRIVATE SOLVER_Z3_ENABLED)
endif()

if(_camada_backend_link_libs)
  # LINK_GROUP RESCAN only applies under linkers that advertise support for it
  # (GNU ld / lld / mold via --start-group/--end-group). Apple ld and MSVC's
  # link.exe iterate by default and don't expose RESCAN at all — passing the
  # generator expression there causes "Feature 'RESCAN' is not supported for the
  # 'CXX' link language" at generate time. Restrict the wrap to the static
  # Linux/BSD path; on every other configuration use a plain link list.
  if(NOT BUILD_SHARED_LIBS
     AND NOT MSVC
     AND NOT CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    target_link_libraries(
      ${LIBRARY_TARGET_NAME}
      PUBLIC "$<LINK_GROUP:RESCAN,${_camada_backend_link_libs}>")
  else()
    target_link_libraries(${LIBRARY_TARGET_NAME}
                          PUBLIC ${_camada_backend_link_libs})
  endif()
endif()

if(CAMADA_SOLVER_SMTLIB_ENABLE)
  target_compile_definitions(${LIBRARY_TARGET_NAME}
                             PRIVATE SOLVER_SMTLIB_ENABLED)
endif()

# Set two minimum target properties for the library. See
# https://cmake.org/cmake/help/latest/command/set_target_properties.html
# Properties are: 1) Library version number 2) list of corresponding public
# headers
set_target_properties(
  ${LIBRARY_TARGET_NAME}
  PROPERTIES VERSION ${${PROJECT_NAME}_VERSION}
             SOVERSION ${CAMADA_VER_MAJOR}
             PUBLIC_HEADER "${${LIBRARY_TARGET_NAME}_PUB_HDR}")

# Specify include directories for both compilation and installation process. The
# $<INSTALL_PREFIX> generator expression is useful to ensure to create
# relocatable configuration files, see
# https://cmake.org/cmake/help/latest/manual/cmake-packages.7.html#creating-relocatable-packages
target_include_directories(
  ${LIBRARY_TARGET_NAME}
  PUBLIC
    "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
    "$<INSTALL_INTERFACE:$<INSTALL_PREFIX>/${CMAKE_INSTALL_INCLUDEDIR}>"
    "$<INSTALL_INTERFACE:$<INSTALL_PREFIX>/${CMAKE_INSTALL_INCLUDEDIR}/${LIBRARY_TARGET_NAME}>"
)

# Specify installation targets, typology and destination folders.
install(
  TARGETS ${LIBRARY_TARGET_NAME}
  EXPORT ${PROJECT_NAME}
  LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}" COMPONENT shlib
  ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}" COMPONENT lib
  RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}" COMPONENT bin
  PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/${LIBRARY_TARGET_NAME}"
                COMPONENT dev)

install(
  FILES "${CMAKE_BINARY_DIR}/src/camadafeatures.h"
  DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/${LIBRARY_TARGET_NAME}"
  COMPONENT dev)
