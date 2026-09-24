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

# Where a bare link name is searched for, both when declaring imported targets
# for CVC5's export and when building CAMADA_CVC5_EXTRA_LIBS below.
set(_camada_cvc5_lib_hints
    ${CAMADA_DEPS_INSTALL_DIR}/lib ${CAMADA_DEPS_INSTALL_DIR}/lib64
    ${CAMADA_SOLVER_CVC5_DIR}/lib ${CAMADA_SOLVER_CVC5_DIR}/lib64
    ${CAMADA_CVC5_DIR}/lib ${CAMADA_CVC5_DIR}/lib64)

# CVC5's export names its static dependencies by bare name
# ($<LINK_ONLY:cadical>, picpoly, picpolyxx, gmp, mpfr). CMake resolves a bare
# name against a target of that name when one exists and otherwise emits
# -lcadical, which leaves the archive to the linker's default search path: that
# resolves on Linux, where these sit in /usr/lib, and fails on Homebrew, whose
# /opt/homebrew/lib is not searched ("library 'mpfr' not found"). Declaring an
# imported target per name makes the export resolve on its own. The prebuilt
# recipe instead rewrote CVC5's installed cvc5Targets.cmake, keyed on a literal
# substring that a differently-formatted export would have stopped matching
# silently.
#
# CaDiCaL passes its archive explicitly: it must be the one shared build, not
# whatever copy find_library turns up, since a second CaDiCaL is the layout
# clash this whole arrangement exists to prevent. The rest are searched for.
macro(_camada_declare_bare_link_target _name)
  if(NOT TARGET ${_name})
    set(_camada_bare_path "${ARGN}")
    if(NOT _camada_bare_path)
      # find_library caches its result, which would both leak the name into
      # CMakeCache.txt and short-circuit a later search after the archive moves.
      # The imported target is what carries the path from here on.
      find_library(
        _camada_bare_path_${_name}
        NAMES ${_name}
        HINTS ${_camada_cvc5_lib_hints})
      set(_camada_bare_path "${_camada_bare_path_${_name}}")
      unset(_camada_bare_path_${_name} CACHE)
    endif()
    if(NOT EXISTS "${_camada_bare_path}")
      # Without a target the bare name degrades to -l${_name}, which resolves
      # against the linker's default search path or not at all -- a late link
      # error, or silently the wrong copy. Say so here instead.
      message(
        WARNING
          "CVC5 names ${_name} in its link interface but no archive was found;"
          " the link will fall back to -l${_name}.")
    else()
      add_library(${_name} UNKNOWN IMPORTED GLOBAL)
      set_target_properties(${_name} PROPERTIES IMPORTED_LOCATION
                                                "${_camada_bare_path}")
      if("${_name}" STREQUAL "cadical")
        set_target_properties(
          cadical PROPERTIES INTERFACE_INCLUDE_DIRECTORIES
                             "${CAMADA_CADICAL_PREFIX}/include")
      endif()
    endif()
  endif()
endmacro()

# CaDiCaL has to exist before its target can point at it, so this runs once CVC5
# has been found -- by then camada_setup_cvc5() has built both, or an external
# CVC5 was already installed. Running it before that would warn about archives
# nothing has built yet.
macro(_camada_declare_cvc5_link_targets)
  camada_setup_shared_cadical()
  _camada_declare_bare_link_target(cadical "${CAMADA_CADICAL_LIB}")
  # gmp comes from the one selection the whole build shares, rather than a
  # search that could land on a different copy from the one the other backends
  # link.
  camada_gmp_library(_camada_cvc5_gmp_lib)
  _camada_declare_bare_link_target(gmp "${_camada_cvc5_gmp_lib}")
  foreach(_camada_bare_lib IN ITEMS picpoly picpolyxx mpfr)
    _camada_declare_bare_link_target(${_camada_bare_lib})
  endforeach()
endmacro()

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
  # A downloaded install is rebuilt when it predates the tag Camada builds, not
  # merely when it fails the minimum: the tree left by the prebuilt recipe is
  # 1.3.4, which clears the floor, so nothing would otherwise replace it and the
  # backend would keep linking the CaDiCaL that prebuilt carried. An external
  # CVC5 the user pointed at is left alone -- only the floor applies to it.
  string(REGEX REPLACE "^cvc5-" "" _camada_cvc5_recipe_version
                       "${CAMADA_CVC5_GIT_TAG}")
  # A plain prefix test, not MATCHES: the install path is a path, and as a regex
  # its dots and slashes would not mean what they look like.
  set(_camada_cvc5_is_downloaded FALSE)
  string(FIND "${cvc5_DIR}" "${CAMADA_DEPS_INSTALL_DIR}" _camada_cvc5_dir_pos)
  if(_camada_cvc5_dir_pos EQUAL 0)
    set(_camada_cvc5_is_downloaded TRUE)
  endif()
  if(_camada_download_cvc5
     AND (CVC5_VERSION VERSION_LESS CVC5_MIN_VERSION
          OR (CVC5_VERSION VERSION_LESS _camada_cvc5_recipe_version
              AND _camada_cvc5_is_downloaded)))
    # FORCE: camada_setup_cvc5 returns early on any existing install, which is
    # exactly the tree being replaced here.
    camada_setup_cvc5(FORCE)
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

  # After every path that can settle on a CVC5 install, including the
  # version-floor rebuild above.
  _camada_declare_cvc5_link_targets()

  # The same names CVC5 exports bare, now as resolved paths for Camada's own
  # link line. _camada_declare_cvc5_link_targets already resolved each one, so
  # read the location back off the imported target instead of searching again.
  foreach(_camada_cvc5_extra_lib_name IN ITEMS cadical picpoly picpolyxx gmp
                                               mpfr)
    if(TARGET ${_camada_cvc5_extra_lib_name})
      get_target_property(_camada_cvc5_extra_lib ${_camada_cvc5_extra_lib_name}
                          IMPORTED_LOCATION)
      if(_camada_cvc5_extra_lib)
        list(APPEND CAMADA_CVC5_EXTRA_LIBS "${_camada_cvc5_extra_lib}")
      endif()
    endif()
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
