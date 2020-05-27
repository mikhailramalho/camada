cmake_minimum_required (VERSION 3.7)
project (Camada LANGUAGES CXX)

set (CAMADA_VERSION_MAJOR 0)
set (CAMADA_VERSION_MINOR 0)
set (CAMADA_VERSION_PATCH 0)
set (CAMADA_VERSION "${CAMADA_VERSION_MAJOR}.${CAMADA_VERSION_MINOR}.${CAMADA_VERSION_PATCH}")

# Adds custom modules and default Options
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/scripts/cmake/")

# Set a default build type if none was specified
set(default_build_type "RelWithDebInfo")
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  message(STATUS "Setting build type to '${default_build_type}' as none was specified.")
  set(CMAKE_BUILD_TYPE "${default_build_type}" CACHE
      STRING "Choose the type of build." FORCE)
  # Set the possible values of build type for cmake-gui
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS
    "Debug" "Release" "MinSizeRel" "RelWithDebInfo" "Sanitizer")
endif()

include(Options)
include(Sanitizers)

# Optimization
include(OptimizationCCache)

option(BUILD_SHARED_LIBS "Build shared library" ON)
option(BUILD_STATIC_LIBS "Build static library" ON)

find_package(Boost REQUIRED)
find_package(fmt)

add_subdirectory(src)

# Generate ac_config.h
configure_file (
 "${CMAKE_CURRENT_SOURCE_DIR}/scripts/cmake/cmake_config.in"
 "${CMAKE_CURRENT_BINARY_DIR}/src/ac_config.h"
)
