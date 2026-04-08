include(CheckCXXSourceRuns)

# Function to check YICES's version
function(check_yices_version yices_include yices_lib)
  # Get lib path
  get_filename_component(yices_lib_path ${yices_lib} PATH)
  set(_camada_yices_probe_libs "${yices_lib}")
  find_library(_camada_yices_probe_gmp gmp)
  if(_camada_yices_probe_gmp)
    list(APPEND _camada_yices_probe_libs "${_camada_yices_probe_gmp}")
  endif()

  try_run(
    YICES_RETURNCODE YICES_COMPILED ${CMAKE_BINARY_DIR}
    ${CMAKE_SOURCE_DIR}/scripts/cmake/try_yices.cpp
    COMPILE_DEFINITIONS -I"${yices_include}" LINK_LIBRARIES -L${yices_lib_path}
                        ${_camada_yices_probe_libs}
    RUN_OUTPUT_VARIABLE SRC_OUTPUT)

  if(NOT YICES_COMPILED)
    message(
      FATAL_ERROR
        "Yices lib found in ${yices_lib_path} but test compilation failed: ${SRC_OUTPUT}"
    )
  endif()

  string(REGEX MATCH "([0-9]*\\.[0-9]*\\.[0-9]*)" yices_version "${SRC_OUTPUT}")
  set(YICES_VERSION_STRING
      ${yices_version}
      PARENT_SCOPE)
endfunction(check_yices_version)

set(_camada_yices_hints ${CAMADA_DEPS_INSTALL_DIR} ${CAMADA_SOLVER_YICES_DIR}
                        ${CAMADA_YICES_DIR} $ENV{HOME}/yices)
camada_should_download_dependency(_camada_download_yices FALSE)

if(_camada_download_yices)
  camada_setup_yices()
endif()

if(BUILD_SHARED_LIBS
   AND CAMADA_YICES_LIB
   AND CAMADA_YICES_LIB MATCHES "\\.a$")
  unset(CAMADA_YICES_LIB CACHE)
endif()

if(NOT BUILD_SHARED_LIBS)
  foreach(_camada_yices_hint IN LISTS _camada_yices_hints)
    if(EXISTS "${_camada_yices_hint}/lib/libyices.a")
      set(CAMADA_YICES_LIB "${_camada_yices_hint}/lib/libyices.a")
      break()
    endif()
  endforeach()
endif()

# Looking for YICES in CAMADA_YICES_INCLUDE_DIR
find_path(
  CAMADA_YICES_INCLUDE_DIR yices.h
  HINTS ${_camada_yices_hints}
  PATH_SUFFIXES include)

if(BUILD_SHARED_LIBS)
  find_library(
    CAMADA_YICES_LIB yices
    HINTS ${_camada_yices_hints}
    PATH_SUFFIXES lib bin)
endif()

if(NOT CAMADA_YICES_LIB)
  find_library(
    CAMADA_YICES_LIB yices
    HINTS ${_camada_yices_hints}
    PATH_SUFFIXES lib bin)
endif()

if((NOT CAMADA_YICES_INCLUDE_DIR OR NOT CAMADA_YICES_LIB)
   AND _camada_download_yices)
  find_path(
    CAMADA_YICES_INCLUDE_DIR yices.h
    HINTS ${_camada_yices_hints}
    PATH_SUFFIXES include)
  find_library(
    CAMADA_YICES_LIB yices
    HINTS ${_camada_yices_hints}
    PATH_SUFFIXES lib bin)
endif()

# Try to check it dynamically, by compiling a small program that prints YICES's
# version
if(CAMADA_YICES_INCLUDE_DIR AND CAMADA_YICES_LIB)
  # We do not have the YICES binary to query for a version. Try to use a small
  # C++ program to detect it via the YICES_get_version() API call.
  check_yices_version(${CAMADA_YICES_INCLUDE_DIR} ${CAMADA_YICES_LIB})
endif()

if(_camada_download_yices
   AND CAMADA_YICES_INCLUDE_DIR
   AND CAMADA_YICES_LIB
   AND YICES_VERSION_STRING
   AND Yices_FIND_VERSION
   AND YICES_VERSION_STRING VERSION_LESS Yices_FIND_VERSION)
  camada_setup_yices()
  unset(CAMADA_YICES_INCLUDE_DIR CACHE)
  unset(CAMADA_YICES_LIB CACHE)
  find_path(
    CAMADA_YICES_INCLUDE_DIR yices.h
    HINTS ${_camada_yices_hints}
    PATH_SUFFIXES include)
  find_library(
    CAMADA_YICES_LIB yices
    HINTS ${_camada_yices_hints}
    PATH_SUFFIXES lib bin)
  if(CAMADA_YICES_INCLUDE_DIR AND CAMADA_YICES_LIB)
    check_yices_version(${CAMADA_YICES_INCLUDE_DIR} ${CAMADA_YICES_LIB})
  endif()
endif()

# Hack needed for Ubuntu, since it is not linking with static libs from system
if(DEFINED GMP_DIR)
  find_library(
    LIBGMP_CUSTOM gmp
    NAMES libgmp.a
    PATHS ${GMP_DIR}
    PATH_SUFFIXES lib
    NO_DEFAULT_PATH)
  message(STATUS "Custom gmp for yices found: ${LIBGMP_CUSTOM}")
  list(APPEND CAMADA_YICES_LIB "${LIBGMP_CUSTOM}")
endif()

# handle the QUIETLY and REQUIRED arguments and set YICES_FOUND to TRUE if all
# listed variables are TRUE
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  Yices
  REQUIRED_VARS CAMADA_YICES_LIB CAMADA_YICES_INCLUDE_DIR
  VERSION_VAR YICES_VERSION_STRING)

mark_as_advanced(CAMADA_YICES_LIB CAMADA_YICES_INCLUDE_DIR)
