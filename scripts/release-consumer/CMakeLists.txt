# Smoke test for a Camada release tarball: configure with CMAKE_PREFIX_PATH
# pointing at the staged ./release directory and build a tiny program that links
# against camada::camada and exercises one or more enabled backends. CI uses
# this to catch packaging regressions in scripts/release.py and the install
# rules — the regular regression suite only validates the in-tree library, not
# the installed package config.

cmake_minimum_required(VERSION 3.22)
project(camada-release-consumer LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

find_package(camada CONFIG REQUIRED)

add_executable(release_consumer main.cpp)
target_link_libraries(release_consumer PRIVATE camada::camada)

enable_testing()
add_test(NAME release_consumer COMMAND release_consumer)

# On Windows, the release tarball ships libz3.dll in release/bin separately from
# the import lib in release/lib. Without it on PATH at run time, the consumer
# process exits with STATUS_DLL_NOT_FOUND (0xc0000135) before main. Resolve the
# bin directory through the same CMAKE_PREFIX_PATH the find_package call used
# and prepend it to PATH for this test only.
if(WIN32)
  foreach(_camada_prefix IN LISTS CMAKE_PREFIX_PATH)
    if(IS_DIRECTORY "${_camada_prefix}/bin")
      file(TO_NATIVE_PATH "${_camada_prefix}/bin" _camada_release_bin_native)
      set_tests_properties(
        release_consumer
        PROPERTIES ENVIRONMENT_MODIFICATION
                   "PATH=path_list_prepend:${_camada_release_bin_native}")
      break()
    endif()
  endforeach()
endif()
