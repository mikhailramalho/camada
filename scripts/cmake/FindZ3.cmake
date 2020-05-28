INCLUDE(CheckCXXSourceRuns)

# Function to check Z3's version
function(check_z3_version z3_include z3_lib)
  # Get lib path
  get_filename_component(z3_lib_path ${z3_lib} PATH)

  try_run(
    Z3_RETURNCODE
    Z3_COMPILED
    ${CMAKE_BINARY_DIR}
    ${CMAKE_SOURCE_DIR}/scripts/cmake/try_z3.cpp
    COMPILE_DEFINITIONS -I"${z3_include}"
    LINK_LIBRARIES -L${z3_lib_path} -lz3
    RUN_OUTPUT_VARIABLE SRC_OUTPUT
  )

  if(Z3_COMPILED)
    string(REGEX REPLACE "([0-9]*\\.[0-9]*\\.[0-9]*)" "\\1"
           z3_version "${SRC_OUTPUT}")
    set(Z3_VERSION_STRING ${z3_version} PARENT_SCOPE)
  endif()
endfunction(check_z3_version)

# Looking for Z3 in LLVM_Z3_INSTALL_DIR
find_path(SOLVER_Z3_INCLUDE_DIR z3.h PATHS ${SOLVER_Z3_DIR} $ENV{HOME}/z3 PATH_SUFFIXES include)

find_library(SOLVER_Z3_LIB z3 libz3 PATHS ${SOLVER_Z3_DIR} $ENV{HOME}/z3 PATH_SUFFIXES lib bin)

if (BUILD_STATIC_LIBS)
  set(SOLVER_Z3_LIB "${SOLVER_Z3_LIB} -pthread -ldl")
endif ()

# Try to check it dynamically, by compiling a small program that
# prints Z3's version
if(SOLVER_Z3_INCLUDE_DIR AND SOLVER_Z3_LIB)
  # We do not have the Z3 binary to query for a version. Try to use
  # a small C++ program to detect it via the Z3_get_version() API call.
  check_z3_version(${SOLVER_Z3_INCLUDE_DIR} ${SOLVER_Z3_LIB})
endif()

# handle the QUIETLY and REQUIRED arguments and set Z3_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(Z3
                                  REQUIRED_VARS SOLVER_Z3_LIB SOLVER_Z3_INCLUDE_DIR
                                  VERSION_VAR Z3_VERSION_STRING)

mark_as_advanced(SOLVER_Z3_INCLUDE_DIR SOLVER_Z3_LIB)
