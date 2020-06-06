# Looking for CVC4 in SOLVER_CVC4_INCLUDE_DIR
find_package(CVC4 REQUIRED PATHS ${SOLVER_CVC4_DIR}/lib/cmake/CVC4 $ENV{HOME}/cvc4)

# Remove any suffix from CVC4's version string
string(REGEX REPLACE "([0-9]\\.[0-9]).*" "\\1" CVC4_VERSION "${CVC4_VERSION}")

set(CVC4_MIN_VERSION "1.6")
if(CVC4_VERSION VERSION_LESS CVC4_MIN_VERSION)
  message(FATAL_ERROR "Expected version ${CVC4_MIN_VERSION} or greater")
endif()

set(SOLVER_CVC4_LIB "CVC4::cvc4")

# handle the QUIETLY and REQUIRED arguments and set CVC4_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(CVC4
                                  REQUIRED_VARS SOLVER_CVC4_LIB
                                  VERSION_VAR CVC4_VERSION)

mark_as_advanced(SOLVER_CVC4_LIB)