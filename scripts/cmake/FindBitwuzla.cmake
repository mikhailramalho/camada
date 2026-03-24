set(_camada_bitwuzla_hints
    ${CAMADA_DEPS_INSTALL_DIR} ${CAMADA_SOLVER_BITWUZLA_DIR}
    ${CAMADA_BITWUZLA_DIR} $ENV{HOME}/bitwuzla)

function(_camada_filter_existing_paths out_var)
  set(_camada_existing_paths)
  foreach(_camada_candidate IN LISTS ARGN)
    if(_camada_candidate MATCHES "^\\$<")
      list(APPEND _camada_existing_paths "${_camada_candidate}")
    elseif(EXISTS "${_camada_candidate}")
      list(APPEND _camada_existing_paths "${_camada_candidate}")
    endif()
  endforeach()
  set(${out_var}
      "${_camada_existing_paths}"
      PARENT_SCOPE)
endfunction()

function(_camada_collect_bitwuzla_pkgconfig_paths out_var)
  set(_camada_bitwuzla_pkgconfig_paths)
  foreach(_camada_bitwuzla_hint IN LISTS _camada_bitwuzla_hints)
    if(_camada_bitwuzla_hint)
      list(
        APPEND
        _camada_bitwuzla_pkgconfig_paths
        "${_camada_bitwuzla_hint}/lib/pkgconfig"
        "${_camada_bitwuzla_hint}/lib64/pkgconfig"
        "${_camada_bitwuzla_hint}/share/pkgconfig")
      file(GLOB _camada_bitwuzla_arch_pkgconfig_paths
           "${_camada_bitwuzla_hint}/lib/*/pkgconfig")
      list(APPEND _camada_bitwuzla_pkgconfig_paths
           ${_camada_bitwuzla_arch_pkgconfig_paths})
    endif()
  endforeach()
  list(REMOVE_DUPLICATES _camada_bitwuzla_pkgconfig_paths)
  set(${out_var}
      "${_camada_bitwuzla_pkgconfig_paths}"
      PARENT_SCOPE)
endfunction()

if(EXISTS "${CAMADA_DEPS_INSTALL_DIR}/include/bitwuzla/c/bitwuzla.h")
  camada_setup_bitwuzla()
endif()

_camada_collect_bitwuzla_pkgconfig_paths(_camada_bitwuzla_pkgconfig_paths)
camada_should_download_dependency(_camada_download_bitwuzla TRUE)

find_package(PkgConfig QUIET)

if(PkgConfig_FOUND)
  set(_camada_bitwuzla_saved_pkg_config_path "$ENV{PKG_CONFIG_PATH}")
  foreach(_camada_bitwuzla_pkgconfig_path IN
          LISTS _camada_bitwuzla_pkgconfig_paths)
    if(EXISTS "${_camada_bitwuzla_pkgconfig_path}")
      if(_camada_bitwuzla_saved_pkg_config_path)
        set(ENV{PKG_CONFIG_PATH}
            "${_camada_bitwuzla_pkgconfig_path}:$ENV{PKG_CONFIG_PATH}")
      else()
        set(ENV{PKG_CONFIG_PATH} "${_camada_bitwuzla_pkgconfig_path}")
      endif()
    endif()
  endforeach()

  pkg_check_modules(Bitwuzla QUIET IMPORTED_TARGET bitwuzla)
  if(TARGET PkgConfig::Bitwuzla)
    get_target_property(_camada_bitwuzla_imported_includes PkgConfig::Bitwuzla
                        INTERFACE_INCLUDE_DIRECTORIES)
    if(_camada_bitwuzla_imported_includes)
      _camada_filter_existing_paths(
        _camada_bitwuzla_sanitized_includes
        ${_camada_bitwuzla_imported_includes})
      set_target_properties(
        PkgConfig::Bitwuzla PROPERTIES INTERFACE_INCLUDE_DIRECTORIES
                                       "${_camada_bitwuzla_sanitized_includes}")
      set(Bitwuzla_INCLUDE_DIRS "${_camada_bitwuzla_sanitized_includes}")
    endif()
  endif()
  set(ENV{PKG_CONFIG_PATH} "${_camada_bitwuzla_saved_pkg_config_path}")
endif()

if(NOT Bitwuzla_FOUND AND _camada_download_bitwuzla)
  camada_setup_bitwuzla()
  _camada_collect_bitwuzla_pkgconfig_paths(_camada_bitwuzla_pkgconfig_paths)

  if(PkgConfig_FOUND)
    set(_camada_bitwuzla_saved_pkg_config_path "$ENV{PKG_CONFIG_PATH}")
    foreach(_camada_bitwuzla_pkgconfig_path IN
            LISTS _camada_bitwuzla_pkgconfig_paths)
      if(EXISTS "${_camada_bitwuzla_pkgconfig_path}")
        if(_camada_bitwuzla_saved_pkg_config_path)
          set(ENV{PKG_CONFIG_PATH}
              "${_camada_bitwuzla_pkgconfig_path}:$ENV{PKG_CONFIG_PATH}")
        else()
          set(ENV{PKG_CONFIG_PATH} "${_camada_bitwuzla_pkgconfig_path}")
        endif()
      endif()
    endforeach()

    pkg_check_modules(Bitwuzla QUIET IMPORTED_TARGET bitwuzla)
    if(TARGET PkgConfig::Bitwuzla)
      get_target_property(_camada_bitwuzla_imported_includes
                          PkgConfig::Bitwuzla INTERFACE_INCLUDE_DIRECTORIES)
      if(_camada_bitwuzla_imported_includes)
        _camada_filter_existing_paths(
          _camada_bitwuzla_sanitized_includes
          ${_camada_bitwuzla_imported_includes})
        set_target_properties(
          PkgConfig::Bitwuzla PROPERTIES INTERFACE_INCLUDE_DIRECTORIES
                                         "${_camada_bitwuzla_sanitized_includes}")
        set(Bitwuzla_INCLUDE_DIRS "${_camada_bitwuzla_sanitized_includes}")
      endif()
    endif()
    set(ENV{PKG_CONFIG_PATH} "${_camada_bitwuzla_saved_pkg_config_path}")
  endif()
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  Bitwuzla
  REQUIRED_VARS Bitwuzla_LINK_LIBRARIES Bitwuzla_INCLUDE_DIRS
  VERSION_VAR Bitwuzla_VERSION)
