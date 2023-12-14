find_package(cryptominisat5 PATHS ${CMAKE_SOURCE_DIR}/deps/install/)

find_package(STP HINTS ${CMAKE_SOURCE_DIR}/deps/install/
             ${CAMADA_STP_DIR}/lib/cmake $ENV{HOME}/stp)
