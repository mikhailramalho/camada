# Smoke test for Camada as a CMake subproject: add the source tree with
# add_subdirectory and build the release consumer's program against the in-tree
# camada::camada target. CI uses this to catch top-level-only paths
# (CMAKE_SOURCE_DIR, CMAKE_BINARY_DIR) and a broken build-tree include layout,
# which neither the regression suite nor the release consumer exercises.

cmake_minimum_required(VERSION 3.24)
project(camada-subproject-consumer LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

get_filename_component(_camada_root "${CMAKE_CURRENT_SOURCE_DIR}/../.."
                       ABSOLUTE)
add_subdirectory("${_camada_root}" camada)
if(NOT DEFINED CAMADA_HAVE_Z3)
  message(FATAL_ERROR "Camada did not hand CAMADA_HAVE_Z3 to its parent")
endif()

add_executable(subproject_consumer
               "${_camada_root}/scripts/release-consumer/main.cpp")
target_link_libraries(subproject_consumer PRIVATE camada::camada)

enable_testing()
add_test(NAME subproject_consumer COMMAND subproject_consumer)
