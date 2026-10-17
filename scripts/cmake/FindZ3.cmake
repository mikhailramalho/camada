include(CheckCXXSourceRuns)

# Function to check Z3's version
function(check_z3_version z3_include z3_lib)
  # Get lib path
  get_filename_component(z3_lib_path ${z3_lib} PATH)

  # A static libz3.a needs Threads and dl whatever Camada itself is built as: Z3
  # is built from source as a static archive everywhere but Windows.
  if(NOT BUILD_SHARED_LIBS OR z3_lib MATCHES "\\.a$")
    find_package(Threads REQUIRED)
    if(Threads_FOUND)
      # Z3's static link interface needs -ldl on Unix-style platforms; MSVC has
      # no `dl` library and `cl` parses `-ldl` as `/dl` (LNK4044), so skip it on
      # Windows. Threads on Windows is satisfied implicitly.
      if(MSVC)
        list(APPEND z3_lib "${CMAKE_THREAD_LIBS_INIT}")
      else()
        list(APPEND z3_lib "${CMAKE_THREAD_LIBS_INIT} -ldl")
      endif()
    endif()
  endif()

  try_run(
    Z3_RETURNCODE Z3_COMPILED ${CMAKE_BINARY_DIR}
    ${CMAKE_SOURCE_DIR}/scripts/cmake/try_z3.cpp
    COMPILE_DEFINITIONS -I"${z3_include}" LINK_LIBRARIES -L${z3_lib_path}
                        ${z3_lib}
    RUN_OUTPUT_VARIABLE SRC_OUTPUT)

  if(NOT Z3_COMPILED)
    message(
      FATAL_ERROR
        "Z3 lib found in ${z3_lib_path} but test compilation failed: ${SRC_OUTPUT}"
    )
  endif()

  string(REGEX MATCH "([0-9]*\\.[0-9]*\\.[0-9]*)" z3_version "${SRC_OUTPUT}")
  set(Z3_VERSION_STRING
      ${z3_version}
      PARENT_SCOPE)
endfunction(check_z3_version)

set(_camada_z3_hints ${CAMADA_DEPS_INSTALL_DIR} ${CAMADA_SOLVER_Z3_DIR}
                     ${CAMADA_Z3_DIR} $ENV{HOME}/z3)
camada_should_download_dependency(_camada_download_z3 TRUE)

# Z3 is built from source in the variant Camada itself is built as (see
# camada_setup_z3), and a static request must not be satisfied by a shared libz3
# co-installed in the same prefix. Windows links the import library by its plain
# name.
if(NOT BUILD_SHARED_LIBS AND NOT WIN32)
  set(_camada_z3_names libz3.a)
else()
  set(_camada_z3_names z3)
endif()

if(_camada_download_z3
   AND (RELEASE_MODE OR EXISTS "${CAMADA_DEPS_INSTALL_DIR}/include/z3.h"))
  camada_setup_z3()
endif()

# A cached library that no longer exists (a tree migrating from the prebuilt
# recipe, whose bin/libz3 setup just replaced) is searched for again rather than
# trusted.
if(CAMADA_Z3_LIB)
  set(_camada_z3_cached_static FALSE)
  if(CAMADA_Z3_LIB MATCHES "\\.a$")
    set(_camada_z3_cached_static TRUE)
  endif()
  set(_camada_z3_want_static FALSE)
  if(NOT BUILD_SHARED_LIBS AND NOT WIN32)
    set(_camada_z3_want_static TRUE)
  endif()
  if(NOT EXISTS "${CAMADA_Z3_LIB}" OR NOT _camada_z3_cached_static STREQUAL
                                      _camada_z3_want_static)
    unset(CAMADA_Z3_LIB CACHE)
  endif()
endif()

# Looking for Z3 in CAMADA_Z3_INCLUDE_DIR
find_path(
  CAMADA_Z3_INCLUDE_DIR z3.h
  HINTS ${_camada_z3_hints}
  PATH_SUFFIXES include)

find_library(
  CAMADA_Z3_LIB
  NAMES ${_camada_z3_names}
  HINTS ${_camada_z3_hints}
  PATH_SUFFIXES lib bin)

if((NOT CAMADA_Z3_INCLUDE_DIR OR NOT CAMADA_Z3_LIB) AND _camada_download_z3)
  camada_setup_z3()
  find_path(
    CAMADA_Z3_INCLUDE_DIR z3.h
    HINTS ${_camada_z3_hints}
    PATH_SUFFIXES include)
  find_library(
    CAMADA_Z3_LIB
    NAMES ${_camada_z3_names}
    HINTS ${_camada_z3_hints}
    PATH_SUFFIXES lib bin)
endif()

# Try to check it dynamically, by compiling a small program that prints Z3's
# version
if(CAMADA_Z3_INCLUDE_DIR AND CAMADA_Z3_LIB)
  # We do not have the Z3 binary to query for a version. Try to use a small C++
  # program to detect it via the Z3_get_version() API call.
  check_z3_version(${CAMADA_Z3_INCLUDE_DIR} ${CAMADA_Z3_LIB})
endif()

if(_camada_download_z3
   AND CAMADA_Z3_INCLUDE_DIR
   AND CAMADA_Z3_LIB
   AND Z3_VERSION_STRING
   AND Z3_FIND_VERSION
   AND Z3_VERSION_STRING VERSION_LESS Z3_FIND_VERSION)
  camada_setup_z3()
  unset(CAMADA_Z3_INCLUDE_DIR CACHE)
  unset(CAMADA_Z3_LIB CACHE)
  find_path(
    CAMADA_Z3_INCLUDE_DIR z3.h
    HINTS ${_camada_z3_hints}
    PATH_SUFFIXES include)
  find_library(
    CAMADA_Z3_LIB
    NAMES ${_camada_z3_names}
    HINTS ${_camada_z3_hints}
    PATH_SUFFIXES lib bin)
  if(CAMADA_Z3_INCLUDE_DIR AND CAMADA_Z3_LIB)
    check_z3_version(${CAMADA_Z3_INCLUDE_DIR} ${CAMADA_Z3_LIB})
  endif()
endif()

# Z3 5.3 registers its tactics through inline global variables, i.e. static
# initializers in the translation units that define them. Linked from a static
# archive the normal way, the linker drops every member nothing references, the
# initializers never run, and z3::tactic(c, "smt") finds no tactic at all. Link
# the archive whole so they are kept. CAMADA_Z3_LIB stays the plain path: its
# directory feeds the rpath logic.
set(CAMADA_Z3_LINK_LIBRARIES "${CAMADA_Z3_LIB}")
if(CAMADA_Z3_LIB MATCHES "\\.a$")
  set(CAMADA_Z3_LINK_LIBRARIES "$<LINK_LIBRARY:WHOLE_ARCHIVE,${CAMADA_Z3_LIB}>")
endif()

# Alright, now create a list with z3 and it's dependencies. -ldl is Unix-only;
# MSVC has no `dl` library and would emit LNK4044 silently swallowing the flag.
# Threads on Windows is satisfied implicitly.
if(NOT BUILD_SHARED_LIBS OR CAMADA_Z3_LIB MATCHES "\\.a$")
  find_package(Threads REQUIRED)
  if(Threads_FOUND)
    list(APPEND CAMADA_Z3_LIB "${CMAKE_THREAD_LIBS_INIT}")
    list(APPEND CAMADA_Z3_LINK_LIBRARIES "${CMAKE_THREAD_LIBS_INIT}")
    if(NOT MSVC)
      list(APPEND CAMADA_Z3_LIB "-ldl")
      list(APPEND CAMADA_Z3_LINK_LIBRARIES "-ldl")
    endif()
  endif()
endif()

# handle the QUIETLY and REQUIRED arguments and set Z3_FOUND to TRUE if all
# listed variables are TRUE
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  Z3
  REQUIRED_VARS CAMADA_Z3_LIB CAMADA_Z3_INCLUDE_DIR
  VERSION_VAR Z3_VERSION_STRING)

mark_as_advanced(CAMADA_Z3_LIB CAMADA_Z3_INCLUDE_DIR)
