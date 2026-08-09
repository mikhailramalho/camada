set(_camada_cvc5_hints
    ${CAMADA_DEPS_INSTALL_DIR}
    ${CAMADA_SOLVER_CVC5_DIR}
    ${CAMADA_SOLVER_CVC5_DIR}/lib/cmake
    ${CAMADA_SOLVER_CVC5_DIR}/lib64/cmake
    ${CAMADA_CVC5_DIR}
    ${CAMADA_CVC5_DIR}/lib/cmake
    ${CAMADA_CVC5_DIR}/lib64/cmake
    $ENV{HOME}/cvc5)
camada_should_download_dependency(_camada_download_cvc5 TRUE)

find_package(cvc5 CONFIG QUIET HINTS ${_camada_cvc5_hints})
set(CVC5_FOUND ${cvc5_FOUND})

if(NOT CVC5_FOUND AND _camada_download_cvc5)
  camada_setup_cvc5()
  find_package(cvc5 CONFIG QUIET HINTS ${_camada_cvc5_hints})
  set(CVC5_FOUND ${cvc5_FOUND})
endif()

set(CAMADA_CVC5_EXTRA_LIBS "")
if(CVC5_FOUND)
  # Remove any suffix from CVC5's version string
  string(REGEX REPLACE "([0-9]\\.[0-9]\\.[0-9]).*" "\\1" CVC5_VERSION
                       "${cvc5_VERSION}")

  set(CVC5_MIN_VERSION "1.0.8")
  if(CVC5_VERSION VERSION_LESS CVC5_MIN_VERSION AND _camada_download_cvc5)
    camada_setup_cvc5()
    find_package(cvc5 CONFIG QUIET HINTS ${_camada_cvc5_hints})
    set(CVC5_FOUND ${cvc5_FOUND})
    if(CVC5_FOUND)
      string(REGEX REPLACE "([0-9]\\.[0-9]\\.[0-9]).*" "\\1" CVC5_VERSION
                           "${cvc5_VERSION}")
    endif()
  endif()

  if(CVC5_VERSION VERSION_LESS CVC5_MIN_VERSION)
    message(FATAL_ERROR "Expected version ${CVC5_MIN_VERSION} or greater")
  endif()

  set(_camada_cvc5_lib_hints
      ${CAMADA_DEPS_INSTALL_DIR}/lib ${CAMADA_DEPS_INSTALL_DIR}/lib64
      ${CAMADA_SOLVER_CVC5_DIR}/lib ${CAMADA_SOLVER_CVC5_DIR}/lib64
      ${CAMADA_CVC5_DIR}/lib ${CAMADA_CVC5_DIR}/lib64)
  # gmp is here because cvc5::cvc5's interface pulls it in by bare name; once
  # the link switches to resolved paths below, it must be resolved too (it may
  # only exist as a system library, hence no HINTS restraint).
  foreach(_camada_cvc5_extra_lib_name IN ITEMS cadical picpoly picpolyxx gmp)
    find_library(
      _camada_cvc5_extra_lib
      NAMES ${_camada_cvc5_extra_lib_name}
      HINTS ${_camada_cvc5_lib_hints})
    if(_camada_cvc5_extra_lib)
      list(APPEND CAMADA_CVC5_EXTRA_LIBS "${_camada_cvc5_extra_lib}")
    endif()
    unset(_camada_cvc5_extra_lib CACHE)
  endforeach()

  # cvc5's export names its build configuration "PRODUCTION", so the location
  # has to be looked up through IMPORTED_CONFIGURATIONS rather than assuming the
  # RELEASE convention.
  get_target_property(_camada_cvc5_location cvc5::cvc5 IMPORTED_LOCATION)
  if(NOT _camada_cvc5_location)
    get_target_property(_camada_cvc5_configs cvc5::cvc5 IMPORTED_CONFIGURATIONS)
    if(_camada_cvc5_configs)
      foreach(_camada_cvc5_config IN LISTS _camada_cvc5_configs)
        get_target_property(_camada_cvc5_location cvc5::cvc5
                            IMPORTED_LOCATION_${_camada_cvc5_config})
        if(_camada_cvc5_location)
          break()
        endif()
      endforeach()
    endif()
  endif()

  # Same self-contained-export treatment as STP: exporting the imported target
  # *name* forces consumers through find_package(cvc5), whose static export
  # references its bundled archives (cadical, picpoly) by bare name with no link
  # directory attached. Absolute paths sidestep both. The include dirs travel
  # separately since dropping the target from the link line also drops its usage
  # requirements.
  get_target_property(_camada_cvc5_includes cvc5::cvc5
                      INTERFACE_INCLUDE_DIRECTORIES)
  if(_camada_cvc5_includes)
    set(CVC5_INCLUDE_DIRS "${_camada_cvc5_includes}")
  endif()
  if(_camada_cvc5_location)
    set(CVC5_LINK_LIBRARIES "${_camada_cvc5_location}")
  else()
    set(CVC5_LINK_LIBRARIES cvc5::cvc5)
  endif()

  if(_camada_cvc5_location)
    message(
      STATUS
        "Found CVC5: ${_camada_cvc5_location} (found suitable version \"${CVC5_VERSION}\", minimum required is \"${CVC5_MIN_VERSION}\")"
    )
  else()
    message(
      STATUS
        "Found CVC5: cvc5::cvc5 (found suitable version \"${CVC5_VERSION}\", minimum required is \"${CVC5_MIN_VERSION}\")"
    )
  endif()
endif()
