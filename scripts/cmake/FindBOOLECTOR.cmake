# Looking for Boolector in SOLVER_BOOLECTOR_INCLUDE_DIR
find_package(Boolector REQUIRED PATHS ${SOLVER_BOOLECTOR_DIR}/lib/cmake $ENV{HOME}/boolector)

if(Boolector_FOUND)

  set(SOLVER_BOOLECTOR_LIB "Boolector::boolector")

  # handle the QUIETLY and REQUIRED arguments and set BOOLECTOR_FOUND to TRUE if
  # all listed variables are TRUE
  include(FindPackageHandleStandardArgs)
  FIND_PACKAGE_HANDLE_STANDARD_ARGS(BOOLECTOR
                                    REQUIRED_VARS SOLVER_BOOLECTOR_LIB
                                    VERSION_VAR BOOLECTOR_VERSION)

  mark_as_advanced(SOLVER_BOOLECTOR_LIB)
endif()