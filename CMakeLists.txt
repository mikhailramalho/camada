cmake_minimum_required (VERSION 3.7)
project (Camada LANGUAGES CXX)

#-----------------------------------------------------------------------------#
# Version number

set (CAMADA_VERSION_MAJOR 0)
set (CAMADA_VERSION_MINOR 0)
set (CAMADA_VERSION_PATCH 0)
set (CAMADA_VERSION "${CAMADA_VERSION_MAJOR}.${CAMADA_VERSION_MINOR}.${CAMADA_VERSION_PATCH}")

#-----------------------------------------------------------------------------#
# General macros

# 3-valued option IGNORE/OFF/ON
macro(option3vl var description)
  set(${var} IGNORE CACHE STRING "${description}")
  # Provide drop down menu options in cmake-gui
  set_property(CACHE ${var} PROPERTY STRINGS IGNORE ON OFF)
endmacro()

# Set option only if it still has initial value IGNORE (do not overwrite user
# configurations)
macro(set_option var value)
  if(${var} STREQUAL "IGNORE")
    set(${var} ${value} CACHE STRING "" FORCE)
  endif()
endmacro()

# Macro to configure a solver
macro(config_solver name version)
  # Solver Base dir, it will be used to try to find the libs and headers
  set(SOLVER_${name}_DIR "" CACHE STRING "Directory of the ${name} solver (optional)")

  # Define the options
  option3vl(CAMADA_ENABLE_SOLVER_${name} "Build Camada with ${name}")

  # Try to find the solver and version
  find_package(${name} ${version})

  # If the solver was found, enable it _IF_ the user did not explicitly disable it
  if(${name}_FOUND)
    set_option(CAMADA_ENABLE_SOLVER_${name} ON)
  endif()

  # Set the variable to enable the solver to 0, if the solver is enabled, it will be set to 1
  set(SOLVER_${name}_ENABLED 0)

  if(CAMADA_ENABLE_SOLVER_${name})

    # If the solver was enabled but we could not find it, throw an error
    if(NOT ${name}_FOUND)
      message(FATAL_ERROR "CAMADA_ENABLE_SOLVER_${name} cannot be enabled when ${name} is not available")
    endif()

    # otherwise, add it to the list of available solvers
    list(APPEND CAMADA_AVAILABLE_SOLVERS "${name}")

    # Set the variable to enable the solver to 1
    set(SOLVER_${name}_ENABLED 1)

    # Add include dirs
    include_directories(${SOLVER_${name}_INCLUDE_DIR})

    # and the libs to the list of solver libs
    list(APPEND CAMADA_SOLVER_LIBS "${SOLVER_${name}_LIB}")
  endif()
endmacro()

#-----------------------------------------------------------------------------#
# Adds custom modules
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/scripts/cmake/")

include(Sanitizers)
include(OptimizationCCache)

#-----------------------------------------------------------------------------#
# General options

# Set a default build type if none was specified
set(default_build_type "RelWithDebInfo")
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  message(STATUS "Setting build type to '${default_build_type}' as none was specified")
  set(CMAKE_BUILD_TYPE "${default_build_type}" CACHE
      STRING "Choose the type of build" FORCE)
  # Set the possible values of build type for cmake-gui
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS
    "Debug" "Release" "MinSizeRel" "RelWithDebInfo" "Sanitizer")
endif()

option(ENABLE_WERROR "All warnings are treated as errors during compilation (default: OFF)" OFF)

option(ENABLE_WALL "Enable -Wall during compilation (default: OFF)" OFF)
if(ENABLE_WALL)
  add_definitions(-Wall)
endif()

# Demand C++17
set (CMAKE_CXX_STANDARD 17)

# Used by try_compile
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Generate compile commands by default
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Build only shared by default
option(BUILD_SHARED_LIBS "Build shared library" ON)

# Check for required packages
find_package(fmt REQUIRED)

#-----------------------------------------------------------------------------#
# Solvers

config_solver(Z3 4.8.4)
config_solver(MATHSAT 5.6.3)

#-----------------------------------------------------------------------------#
# Generate ac_config.h

configure_file (
 "${CMAKE_CURRENT_SOURCE_DIR}/scripts/cmake/cmake_config.in"
 "${CMAKE_CURRENT_BINARY_DIR}/src/ac_config.h"
)

#-----------------------------------------------------------------------------#
# Define targets

add_subdirectory(src)

#-----------------------------------------------------------------------------#
# Tests

option(CAMADA_ENABLE_REGRESSION "Enable regression testing" OFF)

if(CAMADA_ENABLE_REGRESSION)
  include(CTest)
  find_package(Catch2 REQUIRED)
  enable_testing()
  add_subdirectory(regression)
endif()

#-----------------------------------------------------------------------------#
# Print Camada configuration

if(NOT WIN32)
  string(ASCII 27 Esc)
  set(Green "${Esc}[32m")
  set(Blue "${Esc}[34m")
  set(ResetColor "${Esc}[m")
endif()

macro(config_info msg value)
  message(STATUS  "${Blue}${msg}: ${Green}${value}${ResetColor}")
endmacro()

macro(config_info_bool msg value)
  if(${value})
    config_info("${msg}" "yes")
  else()
    config_info("${msg}" "no")
  endif()
endmacro()

config_info("Build type" "${CMAKE_BUILD_TYPE}")
config_info_bool("Shared build" "${BUILD_SHARED_LIBS}")

config_info_bool("Solver Z3" "${CAMADA_ENABLE_SOLVER_Z3}")
config_info_bool("Solver MathSAT" "${CAMADA_ENABLE_SOLVER_MATHSAT}")
