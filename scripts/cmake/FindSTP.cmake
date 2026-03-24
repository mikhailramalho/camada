set(_camada_stp_hints ${CAMADA_DEPS_INSTALL_DIR} ${CAMADA_SOLVER_STP_DIR}
                      ${CAMADA_SOLVER_STP_DIR}/lib/cmake ${CAMADA_STP_DIR}
                      ${CAMADA_STP_DIR}/lib/cmake $ENV{HOME}/stp)
camada_should_download_dependency(_camada_download_stp TRUE)

function(_camada_validate_stp)
  set(_camada_stp_include_dirs "${STP_INCLUDE_DIRS}")
  if(TARGET stp)
    get_target_property(_camada_stp_target_include_dirs stp
                        INTERFACE_INCLUDE_DIRECTORIES)
    if(_camada_stp_target_include_dirs)
      list(APPEND _camada_stp_include_dirs ${_camada_stp_target_include_dirs})
    endif()
  endif()

  foreach(_camada_stp_include_dir IN LISTS _camada_stp_include_dirs)
    if(EXISTS "${_camada_stp_include_dir}/stp/c_interface.h")
      set(STP_FOUND TRUE PARENT_SCOPE)
      set(STP_INCLUDE_DIRS "${_camada_stp_include_dir}" PARENT_SCOPE)
      return()
    endif()
  endforeach()

  set(STP_FOUND FALSE PARENT_SCOPE)
  unset(STP_INCLUDE_DIRS PARENT_SCOPE)
endfunction()

function(_camada_normalize_stp_target)
  if(NOT TARGET stp)
    return()
  endif()

  if(STP_INCLUDE_DIRS)
    set_property(TARGET stp PROPERTY INTERFACE_INCLUDE_DIRECTORIES
                                      "${STP_INCLUDE_DIRS}")
  endif()

  set(_camada_stp_minisat_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libminisat.a")
  set(_camada_stp_cryptominisat_lib
      "${CAMADA_DEPS_INSTALL_DIR}/lib/libcryptominisat5.a")

  if(EXISTS "${_camada_stp_minisat_lib}" AND EXISTS "${_camada_stp_cryptominisat_lib}")
    set_property(TARGET stp PROPERTY INTERFACE_LINK_LIBRARIES
                                      "${_camada_stp_minisat_lib};${_camada_stp_cryptominisat_lib}")
  elseif(TARGET minisat AND TARGET libcryptominisat5)
    set_property(TARGET stp PROPERTY INTERFACE_LINK_LIBRARIES
                                      "minisat;libcryptominisat5")
  elseif(TARGET minisat)
    set_property(TARGET stp PROPERTY INTERFACE_LINK_LIBRARIES "minisat")
  endif()
endfunction()

set(_camada_stp_find_args CONFIG QUIET HINTS ${_camada_stp_hints})

if(NOT CAMADA_SOLVER_STP_DIR AND NOT CAMADA_STP_DIR)
  set(STP_DIR "" CACHE PATH "Cleared stale STP cache entry" FORCE)
  list(APPEND _camada_stp_find_args NO_CMAKE_PACKAGE_REGISTRY
       NO_CMAKE_SYSTEM_PACKAGE_REGISTRY)
endif()

find_package(cryptominisat5 CONFIG QUIET HINTS ${_camada_stp_hints})
find_package(minisat CONFIG QUIET HINTS ${_camada_stp_hints})
find_package(STP ${_camada_stp_find_args})
_camada_normalize_stp_target()
_camada_validate_stp()

if(NOT STP_FOUND AND _camada_download_stp)
  camada_setup_stp()
  find_package(cryptominisat5 CONFIG QUIET HINTS ${_camada_stp_hints})
  find_package(minisat CONFIG QUIET HINTS ${_camada_stp_hints})
  find_package(STP CONFIG QUIET HINTS ${_camada_stp_hints}
               NO_CMAKE_PACKAGE_REGISTRY NO_CMAKE_SYSTEM_PACKAGE_REGISTRY)
  _camada_normalize_stp_target()
  _camada_validate_stp()
endif()

if(STP_FOUND)
  get_target_property(_camada_stp_location stp IMPORTED_LOCATION)
  if(NOT _camada_stp_location)
    get_target_property(_camada_stp_location stp IMPORTED_LOCATION_RELEASE)
  endif()
  if(_camada_stp_location)
    message(
      STATUS
        "Found STP: ${_camada_stp_location} (found suitable version \"${STP_FIND_VERSION}\")"
    )
  else()
    message(STATUS "Found STP: stp")
  endif()
endif()
