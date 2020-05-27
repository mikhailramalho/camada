# Module to list Camada Options

#############################
# ABOUT
#############################

#[[
This module sets all default options and variables with default values
to overwrite use the cmake cli, e.g -DENABLE_WERROR=On

Also, you can set some variables which are not defined directly here:
-DCMAKE_BUILD_TYPE which can be Release, Debug, RelWithDebInfo, etc (https://cmake.org/cmake/help/latest/variable/CMAKE_BUILD_TYPE.html)
-G which can be Ninja, Unix Makefile, Visual studio, etc...
]]

#############################
# GENERAL
#############################

option(ENABLE_WERROR "All warnings are treated as errors during compilation (default: OFF)" OFF)

# Demand C++14
set (CMAKE_CXX_STANDARD 14)

# Used by try_compile
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Generate compile commands by default
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)