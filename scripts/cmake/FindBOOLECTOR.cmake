# Looking for Boolector in SOLVER_BOOLECTOR_INCLUDE_DIR
find_package(Boolector HINTS ${SOLVER_BOOLECTOR_DIR}/lib/cmake $ENV{HOME}/boolector)
