set(_camada_stp_hints
    ${CAMADA_DEPS_INSTALL_DIR} ${CAMADA_SOLVER_STP_DIR}
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
      set(STP_FOUND
          TRUE
          PARENT_SCOPE)
      set(STP_INCLUDE_DIRS
          "${_camada_stp_include_dir}"
          PARENT_SCOPE)
      return()
    endif()
  endforeach()

  set(STP_FOUND
      FALSE
      PARENT_SCOPE)
  unset(STP_INCLUDE_DIRS PARENT_SCOPE)
endfunction()

# STP 2.4.0's exported interface references the libabc-pic *target*, which
# STPTargets.cmake never defines (STP builds the archive but does not export the
# target); every consumer that loads the file fails at generate time evaluating
# $<TARGET_FILE:libabc-pic>. Repair our staged copy in place, pointing the
# reference at the staged archive. Only the file under the camada deps tree is
# touched.
function(_camada_repair_stp_targets_file)
  set(_camada_stp_targets_file
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/STP/STPTargets.cmake")
  set(_camada_stp_abc_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libabc-pic.a")
  if(NOT EXISTS "${_camada_stp_targets_file}" OR NOT EXISTS
                                                 "${_camada_stp_abc_lib}")
    return()
  endif()
  file(READ "${_camada_stp_targets_file}" _camada_stp_targets_content)
  string(FIND "${_camada_stp_targets_content}" "\\$<TARGET_FILE:libabc-pic>"
              _camada_stp_abc_ref)
  if(_camada_stp_abc_ref EQUAL -1)
    return()
  endif()
  string(REPLACE "\\$<TARGET_FILE:libabc-pic>" "${_camada_stp_abc_lib}"
                 _camada_stp_targets_content "${_camada_stp_targets_content}")
  file(WRITE "${_camada_stp_targets_file}" "${_camada_stp_targets_content}")
endfunction()

function(_camada_normalize_stp_target)
  if(NOT TARGET stp)
    return()
  endif()

  if(STP_INCLUDE_DIRS)
    set_property(TARGET stp PROPERTY INTERFACE_INCLUDE_DIRECTORIES
                                     "${STP_INCLUDE_DIRS}")
  endif()

  # Resolve the imported archive so camada's link line — and therefore its
  # installed export — carries absolute paths instead of the imported target
  # name. install(EXPORT) can only record the *name* of an imported target,
  # which forces consumers through find_package(STP) to reconstruct it; paths
  # make the camada package self-contained, matching how every other backend is
  # exported.
  get_target_property(_camada_stp_lib stp IMPORTED_LOCATION)
  if(NOT _camada_stp_lib)
    get_target_property(_camada_stp_lib stp IMPORTED_LOCATION_RELEASE)
  endif()

  set(_camada_stp_minisat_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libminisat.a")
  set(_camada_stp_cryptominisat_lib
      "${CAMADA_DEPS_INSTALL_DIR}/lib/libcryptominisat5.a")

  if(EXISTS "${_camada_stp_minisat_lib}" AND EXISTS
                                             "${_camada_stp_cryptominisat_lib}")
    set(_camada_stp_dep_libs "${_camada_stp_minisat_lib}"
                             "${_camada_stp_cryptominisat_lib}")
    # STP >= 2.4.0 builds ABC as a separate archive instead of folding it into
    # libstp.a.
    set(_camada_stp_abc_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libabc-pic.a")
    if(EXISTS "${_camada_stp_abc_lib}")
      list(APPEND _camada_stp_dep_libs "${_camada_stp_abc_lib}")
    endif()
    # On platforms where CMS's patched cadical/cadiback forks are not bundled
    # into libcryptominisat5.a (macOS), they are staged separately; cadiback
    # references cadical symbols, so it must come first.
    set(_camada_stp_cadiback_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libcadiback.a")
    if(EXISTS "${_camada_stp_cadiback_lib}")
      list(APPEND _camada_stp_dep_libs "${_camada_stp_cadiback_lib}"
           "${CAMADA_DEPS_INSTALL_DIR}/lib/libcadical-cms.a")
    endif()
    set_property(TARGET stp PROPERTY INTERFACE_LINK_LIBRARIES
                                     "${_camada_stp_dep_libs}")
    if(_camada_stp_lib)
      set(STP_LINK_LIBRARIES
          "${_camada_stp_lib};${_camada_stp_dep_libs}"
          PARENT_SCOPE)
      return()
    endif()
  elseif(TARGET minisat AND TARGET libcryptominisat5)
    set_property(TARGET stp PROPERTY INTERFACE_LINK_LIBRARIES
                                     "minisat;libcryptominisat5")
  elseif(TARGET minisat)
    set_property(TARGET stp PROPERTY INTERFACE_LINK_LIBRARIES "minisat")
  endif()

  # System installs (or an unresolvable archive) keep the target-based link;
  # their exported packages are expected to be reconstructable by consumers.
  set(STP_LINK_LIBRARIES
      stp
      PARENT_SCOPE)
endfunction()

set(_camada_stp_find_args CONFIG QUIET HINTS ${_camada_stp_hints})

if(NOT CAMADA_SOLVER_STP_DIR AND NOT CAMADA_STP_DIR)
  set(STP_DIR
      ""
      CACHE PATH "Cleared stale STP cache entry" FORCE)
  list(APPEND _camada_stp_find_args NO_CMAKE_PACKAGE_REGISTRY
       NO_CMAKE_SYSTEM_PACKAGE_REGISTRY)
endif()

find_package(cryptominisat5 CONFIG QUIET HINTS ${_camada_stp_hints})
find_package(minisat CONFIG QUIET HINTS ${_camada_stp_hints})
_camada_repair_stp_targets_file()
find_package(STP ${_camada_stp_find_args})
_camada_normalize_stp_target()
_camada_validate_stp()

if(NOT STP_FOUND AND _camada_download_stp)
  camada_setup_stp()
  find_package(cryptominisat5 CONFIG QUIET HINTS ${_camada_stp_hints})
  find_package(minisat CONFIG QUIET HINTS ${_camada_stp_hints})
  _camada_repair_stp_targets_file()
  find_package(
    STP
    CONFIG
    QUIET
    HINTS
    ${_camada_stp_hints}
    NO_CMAKE_PACKAGE_REGISTRY
    NO_CMAKE_SYSTEM_PACKAGE_REGISTRY)
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
