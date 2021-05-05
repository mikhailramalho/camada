cmake_minimum_required (VERSION 3.7)

set (CAMADA_VER_MAJOR 0)
set (CAMADA_VER_MINOR 0)

project (camada LANGUAGES CXX C VERSION "${CAMADA_VER_MAJOR}.${CAMADA_VER_MINOR}")

#-----------------------------------------------------------------------------#
# General macros

# 3-valued option IFAVAILABLE/OFF/ON
macro(option3vl var description)
  set(${var} IFAVAILABLE CACHE STRING "${description}")
  # Provide drop down menu options in cmake-gui
  set_property(CACHE ${var} PROPERTY STRINGS IFAVAILABLE ON OFF)
endmacro()

# Set option only if it still has initial value IFAVAILABLE (do not overwrite user
# configurations)
macro(set_option var value)
  if(${var} STREQUAL "IFAVAILABLE")
    set(${var} ${value} CACHE STRING "" FORCE)
  endif()
endmacro()

# Macro to configure a solver
macro(config_solver name version)
  # Solver Base dir, it will be used to try to find the libs and headers
  set(SOLVER_${name}_DIR "" CACHE STRING "Directory of the ${name} solver (optional)")

  # Define the options
  option3vl(CAMADA_ENABLE_SOLVER_${name} "Build Camada with ${name}")

  # Set the variable to enable the solver to 0, if the solver is enabled, it will be set to 1
  set(SOLVER_${name}_ENABLED 0)
endmacro()

#-----------------------------------------------------------------------------#

# Defines the CMAKE_INSTALL_LIBDIR, CMAKE_INSTALL_BINDIR and many other useful macros.
# See https://cmake.org/cmake/help/latest/module/GNUInstallDirs.html
include(GNUInstallDirs)

# Control where libraries and executables are placed during the build.
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/${CMAKE_INSTALL_BINDIR}")
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/${CMAKE_INSTALL_LIBDIR}")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/${CMAKE_INSTALL_LIBDIR}")

# To build shared libraries in Windows, we set CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS to TRUE.
set(CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS ON)

# Under MSVC, we set CMAKE_DEBUG_POSTFIX to "d" to add a trailing "d" to library
# built in debug mode.
if(MSVC)
    set(CMAKE_DEBUG_POSTFIX "d")
endif()

# Build position independent code.
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Disable C and C++ compiler extensions.
set(CMAKE_C_EXTENSIONS OFF)
set(CMAKE_CXX_EXTENSIONS OFF)

# Adds custom modules
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/scripts/cmake/")

# Add option to build using sanitizers
include(Sanitizers)

# Enable ccache if available
include(OptimizationCCache)

# Shared/Dynamic or Static library?
option(BUILD_SHARED_LIBS "Build libraries as shared as opposed to static" ON)

option(ENABLE_WARNINGS "Enable -Wall, -Wextra, and -pedantic when compiling (default: OFF)" OFF)
if(ENABLE_WALL)
  add_definitions(-Wall -Wextra -pedantic)
endif()

option(ENABLE_WERROR "All warnings are treated as errors when compiling (default: OFF)" OFF)
if(ENABLE_WERROR)
  add_definitions(-Werror)
endif()

# Demand C++14
set (CMAKE_CXX_STANDARD 14)

# Generate compile commands by default
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Build test related commands
option(CAMADA_ENABLE_REGRESSION "Enable regression testing" OFF)
if(CAMADA_ENABLE_REGRESSION)
  include(CTest)
  find_package(Catch2 REQUIRED)
  enable_testing()
endif()

# Enable RPATH support for installed binaries and libraries
include(AddInstallRPATHSupport)
add_install_rpath_support(BIN_DIRS "${CMAKE_INSTALL_FULL_BINDIR}"
                          LIB_DIRS "${CMAKE_INSTALL_FULL_LIBDIR}"
                          INSTALL_NAME_DIR "${CMAKE_INSTALL_FULL_LIBDIR}"
                          USE_LINK_PATH)

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

# Solvers
config_solver(Z3 4.8.8)
config_solver(MATHSAT 5.6.3)
config_solver(CVC4 1.8)
config_solver(BOOLECTOR 3.2.1)
config_solver(YICES 2.6.1)
config_solver(STP 2.3.3)

# Generate ac_config.h
configure_file (
 "${CMAKE_CURRENT_SOURCE_DIR}/scripts/cmake/cmake_config.in"
 "${CMAKE_CURRENT_BINARY_DIR}/src/ac_config.h"
)

# Define targets
add_subdirectory(src)

# Create and install CMake configuration files for your project that are
# necessary to for other projects to call find_package(LibTemplateCMake).
include(InstallBasicPackageFiles)
install_basic_package_files(${PROJECT_NAME}
                            VERSION ${${PROJECT_NAME}_VERSION}
                            COMPATIBILITY AnyNewerVersion
                            VARS_PREFIX ${PROJECT_NAME}
                            NO_CHECK_REQUIRED_COMPONENTS_MACRO)

# Add the uninstall target
include(AddUninstallTarget)

# Add integration tests (unit tests for each library should be in each sublibrary directory).
if(BUILD_TESTING)
    add_subdirectory(regression)
endif()

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
config_info_bool("Solver CVC4" "${CAMADA_ENABLE_SOLVER_CVC4}")
config_info_bool("Solver Boolector" "${CAMADA_ENABLE_SOLVER_BOOLECTOR}")
config_info_bool("Solver Yices" "${CAMADA_ENABLE_SOLVER_YICES}")
config_info_bool("Solver STP" "${CAMADA_ENABLE_SOLVER_STP}")