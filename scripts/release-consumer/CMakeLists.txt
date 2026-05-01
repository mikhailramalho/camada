# Smoke test for a Camada release tarball: configure with CMAKE_PREFIX_PATH
# pointing at the staged ./release directory and build a tiny program that links
# against camada::camada and exercises one or more enabled backends. CI uses
# this to catch packaging regressions in scripts/release.py and the install
# rules — the regular regression suite only validates the in-tree library, not
# the installed package config.

cmake_minimum_required(VERSION 3.15)
project(camada-release-consumer LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

find_package(camada CONFIG REQUIRED)

add_executable(release_consumer main.cpp)
target_link_libraries(release_consumer PRIVATE camada::camada)

enable_testing()
add_test(NAME release_consumer COMMAND release_consumer)
