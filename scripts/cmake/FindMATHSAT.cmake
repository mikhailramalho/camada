INCLUDE(CheckCXXSourceRuns)

# Function to check MATHSAT's version
function(check_mathsat_version mathsat_include mathsat_lib)
  # Get lib path
  get_filename_component(mathsat_lib_path ${mathsat_lib} PATH)

  if (NOT BUILD_SHARED_LIBS)
    find_package(Threads REQUIRED)
    if(Threads_FOUND)
      set(mathsat_lib "${mathsat_lib} ${CMAKE_THREAD_LIBS_INIT} -ldl")
    endif()
  endif ()

  try_run(
    MATHSAT_RETURNCODE
    MATHSAT_COMPILED
    ${CMAKE_BINARY_DIR}
    ${CMAKE_SOURCE_DIR}/scripts/cmake/try_mathsat.cpp
    COMPILE_DEFINITIONS -I"${mathsat_include}"
    LINK_LIBRARIES -L${mathsat_lib_path} ${mathsat_lib}
    RUN_OUTPUT_VARIABLE SRC_OUTPUT
  )

  if(MATHSAT_COMPILED)
    string(REGEX REPLACE "([0-9]*\\.[0-9]*\\.[0-9]*)" "\\1"
           mathsat_version "${SRC_OUTPUT}")
    set(MATHSAT_VERSION_STRING ${mathsat_version} PARENT_SCOPE)
  endif()
endfunction(check_mathsat_version)

# Looking for MATHSAT in SOLVER_MATHSAT_INCLUDE_DIR
find_path(SOLVER_MATHSAT_INCLUDE_DIR mathsat.h PATHS ${SOLVER_MATHSAT_DIR} $ENV{HOME}/mathsat PATH_SUFFIXES include)

find_library(SOLVER_MATHSAT_LIB mathsat PATHS ${SOLVER_MATHSAT_DIR} $ENV{HOME}/mathsat PATH_SUFFIXES lib bin)

# Try to check it dynamically, by compiling a small program that
# prints MATHSAT's version
if(SOLVER_MATHSAT_INCLUDE_DIR AND SOLVER_MATHSAT_LIB)
  # We do not have the MATHSAT binary to query for a version. Try to use
  # a small C++ program to detect it via the MATHSAT_get_version() API call.
  check_mathsat_version(${SOLVER_MATHSAT_INCLUDE_DIR} ${SOLVER_MATHSAT_LIB})
endif()

# Alright, now create a list with mathsat and it's dependencies
if (NOT BUILD_SHARED_LIBS)
  find_package(Threads REQUIRED)
  if(Threads_FOUND)
    set(SOLVER_MATHSAT_LIB "${SOLVER_MATHSAT_LIB} ${CMAKE_THREAD_LIBS_INIT} -ldl")
  endif()
endif ()

# handle the QUIETLY and REQUIRED arguments and set MATHSAT_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(MATHSAT
                                  REQUIRED_VARS SOLVER_MATHSAT_LIB SOLVER_MATHSAT_INCLUDE_DIR
                                  VERSION_VAR MATHSAT_VERSION_STRING)

mark_as_advanced(SOLVER_MATHSAT_LIB SOLVER_MATHSAT_INCLUDE_DIR)
