# Include binary path so we can include ac_config.h
include_directories(${CMAKE_BINARY_DIR}/src)

# This is the "physical" (i.e. real) name of the library.
# The actual file name of the library built is constructed based on conventions
# of the native platform, such as lib<LIBRARY_TARGET_NAME>.a,
# lib<LIBRARY_TARGET_NAME>.dylib or <LIBRARY_TARGET_NAME>.lib.
set(LIBRARY_TARGET_NAME ${PROJECT_NAME})

# List of CPP (source) library files.
set(${LIBRARY_TARGET_NAME}_SRC
    camada.cpp
    camadaexpr.cpp
    camadasort.cpp
    camadaimpl.cpp
    boolectorsolver.cpp
    cvc4solver.cpp
    mathsatsolver.cpp
    stpsolver.cpp
    yicessolver.cpp
    z3solver.cpp
)

# List of HPP (header) library files.
set(${LIBRARY_TARGET_NAME}_HDR
    camada.h camadasort.h camadaexpr.h camadaimpl.h
)

# Adds a library target called ${LIBRARY_TARGET_NAME} to be built from the
# source and header files listed in the command invocation.
add_library(${LIBRARY_TARGET_NAME} ${${LIBRARY_TARGET_NAME}_SRC} ${${LIBRARY_TARGET_NAME}_HDR})

# Within this project, you can link to this library by just specifing the name
# of the target, i.e. ${LIBRARY_TARGET_NAME} = LibTemplateCMake. It is useful,
# however, to define an alias of this library with the scope of the exported
# library itself because (1) you will link against it with the exact same syntax
# of an imported library and (2) because names having a double-colon (::) are
# always treated as the name of either an alias or imported target. Any attempt
# to use such a name for a different target type will result in an error.
add_library(${PROJECT_NAME}::${LIBRARY_TARGET_NAME} ALIAS ${LIBRARY_TARGET_NAME})

# Set two minimum target properties for the library.
# See https://cmake.org/cmake/help/latest/command/set_target_properties.html
# Properties are: 1) Library version number 2) list of corresponding public headers
set_target_properties(${LIBRARY_TARGET_NAME} PROPERTIES VERSION       ${${PROJECT_NAME}_VERSION}
                                                        PUBLIC_HEADER "${${LIBRARY_TARGET_NAME}_HDR}")

# Specify include directories for both compilation and installation process.
# The $<INSTALL_PREFIX> generator expression is useful to ensure to create
# relocatable configuration files, see https://cmake.org/cmake/help/latest/manual/cmake-packages.7.html#creating-relocatable-packages
target_include_directories(${LIBRARY_TARGET_NAME} PUBLIC "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
                                                         "$<INSTALL_INTERFACE:$<INSTALL_PREFIX>/${CMAKE_INSTALL_INCLUDEDIR}>")

# Specify installation targets, typology and destination folders.
install(TARGETS ${LIBRARY_TARGET_NAME}
        EXPORT  ${PROJECT_NAME}
        LIBRARY       DESTINATION "${CMAKE_INSTALL_LIBDIR}"                            COMPONENT shlib
        ARCHIVE       DESTINATION "${CMAKE_INSTALL_LIBDIR}"                            COMPONENT lib
        RUNTIME       DESTINATION "${CMAKE_INSTALL_BINDIR}"                            COMPONENT bin
        PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/${LIBRARY_TARGET_NAME}" COMPONENT dev)