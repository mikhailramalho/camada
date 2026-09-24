set(CAMADA_DOWNLOAD_DEPENDENCIES
    "OFF"
    CACHE
      STRING
      "Download missing solver dependencies during CMake configure: OFF, ALL, or PERMISSIVE"
)
set_property(CACHE CAMADA_DOWNLOAD_DEPENDENCIES PROPERTY STRINGS OFF ALL
                                                         PERMISSIVE)

if(NOT CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "OFF"
   AND NOT CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "ALL"
   AND NOT CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "PERMISSIVE")
  message(
    FATAL_ERROR
      "CAMADA_DOWNLOAD_DEPENDENCIES must be one of: OFF, ALL, PERMISSIVE")
endif()

set(CAMADA_DEPS_DIR
    "${CMAKE_BINARY_DIR}/deps"
    CACHE PATH "Directory used to store downloaded solver dependencies")
set(CAMADA_DEPS_SRC_DIR
    "${CAMADA_DEPS_DIR}/src"
    CACHE PATH "Directory used to store downloaded solver sources")
set(CAMADA_DEPS_INSTALL_DIR
    "${CAMADA_DEPS_DIR}/install"
    CACHE PATH "Directory used to install downloaded solver dependencies")

set(CAMADA_Z3_LINUX_X86_64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip"
    CACHE STRING
          "URL used to download the prebuilt Z3 archive for Linux x86_64")
set(CAMADA_Z3_LINUX_AARCH64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-glibc-2.34.zip"
    CACHE STRING
          "URL used to download the prebuilt Z3 archive for Linux aarch64")
set(CAMADA_Z3_MACOS_X86_64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-osx-13.7.zip"
    CACHE STRING
          "URL used to download the prebuilt Z3 archive for macOS x86_64")
set(CAMADA_Z3_MACOS_ARM64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-osx-13.7.zip"
    CACHE STRING "URL used to download the prebuilt Z3 archive for macOS arm64")
set(CAMADA_Z3_WINDOWS_X86_64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-win.zip"
    CACHE STRING
          "URL used to download the prebuilt Z3 archive for Windows x86_64")
set(CAMADA_CVC5_LINUX_X86_64_URL
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-x86_64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt cvc5 archive for Linux x86_64")
set(CAMADA_CVC5_LINUX_AARCH64_URL
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-arm64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt cvc5 archive for Linux aarch64")
set(CAMADA_CVC5_MACOS_X86_64_URL
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-macOS-x86_64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt cvc5 archive for macOS x86_64")
set(CAMADA_CVC5_MACOS_ARM64_URL
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-macOS-arm64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt cvc5 archive for macOS arm64")
# No Windows prebuilt for CVC5: cvc5Targets.cmake lists cadical, picpoly,
# picpolyxx, and gmp as bare-name INTERFACE_LINK_LIBRARIES, but the static
# Windows release zip merges them into cvc5.lib without shipping standalone .lib
# files, so MSVC fails with LNK1104 trying to find cadical.lib.

# Three dependencies embed CaDiCaL: Bitwuzla, CVC5, and CryptoMiniSat (which STP
# pulls in). Any two in one binary is the same clash -- one definition survives
# the link while each library keeps the field offsets it was compiled with -- so
# Camada builds one CaDiCaL and every consumer links it, including when it is
# the only backend enabled. Each consumer's setup asks for it directly;
# camada_setup_shared_cadical() is stamped, so the first request builds it and
# the rest return at once. BUILD_SHARED_LIBS does not avoid the clash: these
# arrive as static archives whichever way Camada is built, so every copy would
# land in libcamada.so too.

# CVC5 ships a patched CaDiCaL ("elevate"), Bitwuzla's prebuilt bundles stock
# CaDiCaL inside libbitwuzla.a. A static link of both keeps one definition of
# each of their ~1100 shared symbols while each library's code still computes
# member offsets from the headers it was compiled against -- cvc5 builds CaDiCaL
# with -DQUIET, which drops two members from the middle of CaDiCaL::Internal, so
# the survivor reads every later field at the wrong offset. Bitwuzla then sized
# a Walker allocation from garbage and asked for 8 GB. Building Bitwuzla from
# source against cvc5's exact CaDiCaL leaves one implementation in the binary
# and removes the clash. Source and flags are taken verbatim from cvc5's
# cmake/FindCaDiCaL.cmake so the two agree.
set(CAMADA_CADICAL_URL
    "https://github.com/arminbiere/cadical/archive/rel-2.1.3-elevate.tar.gz"
    CACHE STRING
          "URL of the CaDiCaL source shared by the Bitwuzla and CVC5 backends")
set(CAMADA_CADICAL_SHA256
    "15e1e82f7f9a9da0e97070cb8ac41d5b32139f65d54f72d2ff84849b0466ef92"
    CACHE STRING "Expected SHA256 of the shared CaDiCaL source archive")

# Where the shared CaDiCaL lives. CAMADA_CADICAL_PREFIX is an install-style tree
# (lib/, include/cadical/) that Bitwuzla, CVC5 and FindSTP link from; it sits
# outside CAMADA_DEPS_INSTALL_DIR on purpose, because a second libcadical.a in
# the installed tree is exactly what check-duplicate-sat-engines.py rejects.
# CAMADA_CADICAL_SRC_DIR is the unpacked source, which CryptoMiniSat consumes
# directly as a sibling directory. The archive unpacks to cadical-<tag>/.
get_filename_component(_camada_cadical_archive_name "${CAMADA_CADICAL_URL}"
                       NAME)
string(REGEX REPLACE "\\.tar\\.gz$" "" _camada_cadical_tag
                     "${_camada_cadical_archive_name}")
set(CAMADA_CADICAL_PREFIX "${CAMADA_DEPS_DIR}/cadical")
set(CAMADA_CADICAL_LIB "${CAMADA_CADICAL_PREFIX}/lib/libcadical.a")
set(CAMADA_CADICAL_SRC_DIR
    "${CAMADA_DEPS_SRC_DIR}/cadical-${_camada_cadical_tag}")
set(CAMADA_BITWUZLA_GIT_TAG
    "0.9.1"
    CACHE
      STRING
      "Bitwuzla tag used when building it from source against a shared CaDiCaL")

# Bitwuzla is always built from source (see camada_setup_bitwuzla), so there is
# no prebuilt URL to pin. It is not built on Windows: the Windows CI leg leaves
# it disabled, as ESBMC does.
set(CAMADA_MATHSAT_VERSION
    "5.6.17"
    CACHE STRING "MathSAT release version used for prebuilt downloads")
# The 5.6.17 macOS tarball is mispackaged: libmathsat.a is a plain ar archive
# whose members are fat (universal) Mach-O objects, a layout Apple's ld rejects
# ("archive member ... not a mach-o file"). 5.6.16 shipped the correct lipo
# format (a fat file of two thin archives), so macOS stays pinned there until
# upstream fixes the packaging.
set(CAMADA_MATHSAT_MACOS_VERSION
    "5.6.16"
    CACHE STRING "MathSAT release version used for the macOS prebuilts")
set(CAMADA_MATHSAT_LINUX_X86_64_URL
    "https://mathsat.fbk.eu/release/mathsat-5.6.17-linux-x86_64.tar.gz"
    CACHE STRING "URL used to download MathSAT for Linux x86_64")
set(CAMADA_MATHSAT_LINUX_AARCH64_URL
    "https://mathsat.fbk.eu/release/mathsat-5.6.17-linux-aarch64.tar.gz"
    CACHE STRING "URL used to download MathSAT for Linux aarch64")
set(CAMADA_MATHSAT_MACOS_X86_64_URL
    "https://mathsat.fbk.eu/release/mathsat-${CAMADA_MATHSAT_MACOS_VERSION}-macos.tar.gz"
    CACHE STRING "URL used to download MathSAT for macOS x86_64")
set(CAMADA_MATHSAT_MACOS_ARM64_URL
    "https://mathsat.fbk.eu/release/mathsat-${CAMADA_MATHSAT_MACOS_VERSION}-macos.tar.gz"
    CACHE STRING "URL used to download MathSAT for macOS arm64")
# No Windows prebuilt for MathSAT: mathsat.h pulls in <gmp.h> and Camada calls
# mpq_*/mpz_* APIs directly, but Windows has no system GMP and the win64 vendor
# archive ships only the runtime gmp.dll, no headers.

function(camada_ensure_deps_dirs)
  file(MAKE_DIRECTORY "${CAMADA_DEPS_DIR}")
  file(MAKE_DIRECTORY "${CAMADA_DEPS_SRC_DIR}")
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}")
endfunction()

function(camada_should_download_dependency out_var is_permissive)
  if(CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "ALL")
    set(${out_var}
        TRUE
        PARENT_SCOPE)
    return()
  endif()

  if(CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "PERMISSIVE" AND is_permissive)
    set(${out_var}
        TRUE
        PARENT_SCOPE)
    return()
  endif()

  set(${out_var}
      FALSE
      PARENT_SCOPE)
endfunction()

function(camada_include_cpm)
  if(NOT COMMAND CPMAddPackage)
    if(POLICY CMP0169)
      cmake_policy(SET CMP0169 OLD)
    endif()
    include(CPM)
  endif()
endfunction()

function(camada_run_checked)
  set(options)
  set(one_value_args WORKING_DIRECTORY MESSAGE)
  set(multi_value_args COMMAND)
  cmake_parse_arguments(CAMADA_RUN "${options}" "${one_value_args}"
                        "${multi_value_args}" ${ARGN})

  if(CAMADA_RUN_MESSAGE)
    message(STATUS "${CAMADA_RUN_MESSAGE}")
  endif()

  string(REPLACE ";" " " command_string "${CAMADA_RUN_COMMAND}")
  execute_process(
    COMMAND ${CAMADA_RUN_COMMAND}
    WORKING_DIRECTORY "${CAMADA_RUN_WORKING_DIRECTORY}"
    RESULT_VARIABLE command_result
    OUTPUT_VARIABLE command_stdout
    ERROR_VARIABLE command_stderr)

  if(NOT command_result EQUAL 0)
    message(
      FATAL_ERROR
        "Command failed with exit code ${command_result}\nWorking directory: ${CAMADA_RUN_WORKING_DIRECTORY}\nCommand: ${command_string}\nstdout:\n${command_stdout}\nstderr:\n${command_stderr}"
    )
  endif()
endfunction()

function(camada_find_gmp_header out_var)
  find_path(
    _camada_gmp_header_dir gmp.h
    HINTS ${CAMADA_DEPS_INSTALL_DIR} ${CMAKE_PREFIX_PATH} /opt/homebrew
          /usr/local
    PATH_SUFFIXES include)
  set(${out_var}
      "${_camada_gmp_header_dir}"
      PARENT_SCOPE)
endfunction()

function(camada_find_program_with_prefixes out_var program_name)
  string(TOUPPER "${program_name}" _camada_program_upper)
  set(_camada_program_cache_var "CAMADA_FOUND_PROGRAM_${_camada_program_upper}")
  unset(${_camada_program_cache_var} CACHE)
  find_program(
    ${_camada_program_cache_var} ${program_name}
    HINTS ${CMAKE_PREFIX_PATH} /opt/homebrew /usr/local
    PATH_SUFFIXES bin "opt/${program_name}/bin")
  set(${out_var}
      "${${_camada_program_cache_var}}"
      PARENT_SCOPE)
endfunction()

function(camada_download_file url output_path)
  get_filename_component(output_dir "${output_path}" DIRECTORY)
  file(MAKE_DIRECTORY "${output_dir}")

  if(EXISTS "${output_path}")
    file(SIZE "${output_path}" output_size)
    if(output_size GREATER 0)
      return()
    endif()
    file(REMOVE "${output_path}")
  endif()

  message(STATUS "Downloading ${url}")
  file(
    DOWNLOAD "${url}" "${output_path}"
    STATUS download_status
    LOG download_log
    SHOW_PROGRESS)
  list(GET download_status 0 download_status_code)
  list(GET download_status 1 download_status_message)

  if(download_status_code EQUAL 0)
    file(SIZE "${output_path}" output_size)
    if(output_size GREATER 0)
      return()
    endif()
    set(download_status_message
        "Downloaded file is empty after a successful transfer")
  endif()

  file(REMOVE "${output_path}")

  find_program(CAMADA_CURL_EXECUTABLE curl)
  if(CAMADA_CURL_EXECUTABLE)
    message(STATUS "Retrying download with curl for ${url}")
    execute_process(
      COMMAND ${CAMADA_CURL_EXECUTABLE} -L --fail --output "${output_path}"
              "${url}"
      RESULT_VARIABLE curl_result
      OUTPUT_VARIABLE curl_stdout
      ERROR_VARIABLE curl_stderr)

    if(curl_result EQUAL 0 AND EXISTS "${output_path}")
      file(SIZE "${output_path}" output_size)
      if(output_size GREATER 0)
        return()
      endif()
      file(REMOVE "${output_path}")
      set(curl_stderr "${curl_stderr}\nDownloaded file is empty")
    endif()

    message(
      FATAL_ERROR
        "Failed to download ${url}\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\ncurl exit code: ${curl_result}\nstdout:\n${curl_stdout}\nstderr:\n${curl_stderr}"
    )
  endif()

  message(
    FATAL_ERROR
      "Failed to download ${url}\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\nNo curl executable was found for a retry."
  )
endfunction()

function(camada_try_download_file url output_path result_var)
  get_filename_component(output_dir "${output_path}" DIRECTORY)
  file(MAKE_DIRECTORY "${output_dir}")

  if(EXISTS "${output_path}")
    file(SIZE "${output_path}" output_size)
    if(output_size GREATER 0)
      set(${result_var}
          TRUE
          PARENT_SCOPE)
      return()
    endif()
    file(REMOVE "${output_path}")
  endif()

  message(STATUS "Downloading ${url}")
  file(
    DOWNLOAD "${url}" "${output_path}"
    STATUS download_status
    LOG download_log
    SHOW_PROGRESS)
  list(GET download_status 0 download_status_code)
  list(GET download_status 1 download_status_message)

  if(download_status_code EQUAL 0)
    file(SIZE "${output_path}" output_size)
    if(output_size GREATER 0)
      set(${result_var}
          TRUE
          PARENT_SCOPE)
      return()
    endif()
    set(download_status_message
        "Downloaded file is empty after a successful transfer")
  endif()

  file(REMOVE "${output_path}")

  find_program(CAMADA_CURL_EXECUTABLE curl)
  if(CAMADA_CURL_EXECUTABLE)
    message(STATUS "Retrying download with curl for ${url}")
    execute_process(
      COMMAND ${CAMADA_CURL_EXECUTABLE} -L --fail --output "${output_path}"
              "${url}"
      RESULT_VARIABLE curl_result
      OUTPUT_VARIABLE curl_stdout
      ERROR_VARIABLE curl_stderr)

    if(curl_result EQUAL 0 AND EXISTS "${output_path}")
      file(SIZE "${output_path}" output_size)
      if(output_size GREATER 0)
        set(${result_var}
            TRUE
            PARENT_SCOPE)
        return()
      endif()
      file(REMOVE "${output_path}")
      set(curl_stderr "${curl_stderr}\nDownloaded file is empty")
    endif()

    message(
      WARNING
        "Failed to download ${url}\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\ncurl exit code: ${curl_result}\nstdout:\n${curl_stdout}\nstderr:\n${curl_stderr}"
    )
    set(${result_var}
        FALSE
        PARENT_SCOPE)
    return()
  endif()

  message(
    WARNING
      "Failed to download ${url}\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\nNo curl executable was found for a retry."
  )
  set(${result_var}
      FALSE
      PARENT_SCOPE)
endfunction()

function(camada_extract_archive)
  set(options)
  set(one_value_args ARCHIVE_PATH DESTINATION_DIR MARKER_PATH ARCHIVE_URL
                     SOURCE_DIR)
  cmake_parse_arguments(CAMADA_EXTRACT "${options}" "${one_value_args}" ""
                        ${ARGN})

  if(EXISTS "${CAMADA_EXTRACT_MARKER_PATH}")
    return()
  endif()

  set(_camada_extract_attempt 1)
  while(_camada_extract_attempt LESS_EQUAL 2)
    message(STATUS "Extracting ${CAMADA_EXTRACT_ARCHIVE_PATH}")
    if(CAMADA_EXTRACT_SOURCE_DIR)
      file(REMOVE_RECURSE "${CAMADA_EXTRACT_SOURCE_DIR}")
    endif()
    if(CAMADA_EXTRACT_ARCHIVE_PATH MATCHES "\\.zip$")
      set(_camada_extract_format_args --format=zip)
    else()
      unset(_camada_extract_format_args)
    endif()
    execute_process(
      COMMAND ${CMAKE_COMMAND} -E tar xf "${CAMADA_EXTRACT_ARCHIVE_PATH}"
              ${_camada_extract_format_args}
      WORKING_DIRECTORY "${CAMADA_EXTRACT_DESTINATION_DIR}"
      RESULT_VARIABLE _camada_extract_result
      OUTPUT_VARIABLE _camada_extract_stdout
      ERROR_VARIABLE _camada_extract_stderr)

    if(_camada_extract_result EQUAL 0 AND EXISTS
                                          "${CAMADA_EXTRACT_MARKER_PATH}")
      return()
    endif()

    if(_camada_extract_attempt EQUAL 2)
      message(
        FATAL_ERROR
          "Failed to extract ${CAMADA_EXTRACT_ARCHIVE_PATH}\nexit code: ${_camada_extract_result}\nstdout:\n${_camada_extract_stdout}\nstderr:\n${_camada_extract_stderr}"
      )
    endif()

    message(
      WARNING
        "Extraction failed for ${CAMADA_EXTRACT_ARCHIVE_PATH}. Removing cached archive and partial extraction, then retrying."
    )
    if(CAMADA_EXTRACT_SOURCE_DIR)
      file(REMOVE_RECURSE "${CAMADA_EXTRACT_SOURCE_DIR}")
    endif()
    file(REMOVE "${CAMADA_EXTRACT_ARCHIVE_PATH}")

    if(NOT CAMADA_EXTRACT_ARCHIVE_URL)
      message(
        FATAL_ERROR
          "Failed to extract ${CAMADA_EXTRACT_ARCHIVE_PATH} and no archive URL was provided for a retry."
      )
    endif()

    camada_download_file("${CAMADA_EXTRACT_ARCHIVE_URL}"
                         "${CAMADA_EXTRACT_ARCHIVE_PATH}")
    math(EXPR _camada_extract_attempt "${_camada_extract_attempt} + 1")
  endwhile()
endfunction()

function(camada_stage_prebuilt_tree source_dir)
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}")
  file(COPY "${source_dir}/" DESTINATION "${CAMADA_DEPS_INSTALL_DIR}")
endfunction()

function(camada_select_prebuilt_url output_var package_name)
  if(CMAKE_HOST_SYSTEM_NAME MATCHES "Linux")
    if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64)$")
      if(DEFINED CAMADA_${package_name}_LINUX_X86_64_URL
         AND NOT CAMADA_${package_name}_LINUX_X86_64_URL STREQUAL "")
        set(${output_var}
            "${CAMADA_${package_name}_LINUX_X86_64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    elseif(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)$")
      if(DEFINED CAMADA_${package_name}_LINUX_AARCH64_URL
         AND NOT CAMADA_${package_name}_LINUX_AARCH64_URL STREQUAL "")
        set(${output_var}
            "${CAMADA_${package_name}_LINUX_AARCH64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    endif()
  elseif(CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64)$")
      if(DEFINED CAMADA_${package_name}_MACOS_X86_64_URL
         AND NOT CAMADA_${package_name}_MACOS_X86_64_URL STREQUAL "")
        set(${output_var}
            "${CAMADA_${package_name}_MACOS_X86_64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    elseif(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)$")
      if(DEFINED CAMADA_${package_name}_MACOS_ARM64_URL
         AND NOT CAMADA_${package_name}_MACOS_ARM64_URL STREQUAL "")
        set(${output_var}
            "${CAMADA_${package_name}_MACOS_ARM64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    endif()
  elseif(CMAKE_HOST_SYSTEM_NAME MATCHES "Windows")
    if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(AMD64|x86_64|amd64)$")
      if(DEFINED CAMADA_${package_name}_WINDOWS_X86_64_URL
         AND NOT CAMADA_${package_name}_WINDOWS_X86_64_URL STREQUAL "")
        set(${output_var}
            "${CAMADA_${package_name}_WINDOWS_X86_64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    endif()
  endif()

  message(
    FATAL_ERROR
      "No prebuilt ${package_name} archive configured for host system '${CMAKE_HOST_SYSTEM_NAME}' and processor '${CMAKE_HOST_SYSTEM_PROCESSOR}'"
  )
endfunction()

function(camada_select_mathsat_prebuilt_info output_url_var output_archive_var
         output_source_dir_var)
  if(CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64)$")
      set(${output_url_var}
          "${CAMADA_MATHSAT_MACOS_X86_64_URL}"
          PARENT_SCOPE)
      set(${output_archive_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_MACOS_VERSION}-macos.tar.gz"
          PARENT_SCOPE)
      set(${output_source_dir_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_MACOS_VERSION}-macos"
          PARENT_SCOPE)
      return()
    endif()
    if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)$")
      set(${output_url_var}
          "${CAMADA_MATHSAT_MACOS_ARM64_URL}"
          PARENT_SCOPE)
      set(${output_archive_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_MACOS_VERSION}-macos.tar.gz"
          PARENT_SCOPE)
      set(${output_source_dir_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_MACOS_VERSION}-macos"
          PARENT_SCOPE)
      return()
    endif()
    message(
      FATAL_ERROR
        "No prebuilt MathSAT archive configured for host system '${CMAKE_HOST_SYSTEM_NAME}' and processor '${CMAKE_HOST_SYSTEM_PROCESSOR}'"
    )
  endif()

  if(CMAKE_HOST_SYSTEM_NAME MATCHES "Linux" AND CMAKE_HOST_SYSTEM_PROCESSOR
                                                MATCHES "^(x86_64|amd64)$")
    set(${output_url_var}
        "${CAMADA_MATHSAT_LINUX_X86_64_URL}"
        PARENT_SCOPE)
    set(${output_archive_var}
        "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-linux-x86_64.tar.gz"
        PARENT_SCOPE)
    set(${output_source_dir_var}
        "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-linux-x86_64"
        PARENT_SCOPE)
    return()
  endif()

  if(CMAKE_HOST_SYSTEM_NAME MATCHES "Linux" AND CMAKE_HOST_SYSTEM_PROCESSOR
                                                MATCHES "^(aarch64|arm64)$")
    set(${output_url_var}
        "${CAMADA_MATHSAT_LINUX_AARCH64_URL}"
        PARENT_SCOPE)
    set(${output_archive_var}
        "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-linux-aarch64.tar.gz"
        PARENT_SCOPE)
    set(${output_source_dir_var}
        "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-linux-aarch64"
        PARENT_SCOPE)
    return()
  endif()

  message(
    FATAL_ERROR
      "No prebuilt MathSAT archive configured for host system '${CMAKE_HOST_SYSTEM_NAME}' and processor '${CMAKE_HOST_SYSTEM_PROCESSOR}'"
  )
endfunction()

function(camada_fetch_git_source package_name repository git_tag out_var)
  camada_include_cpm()
  set(FETCHCONTENT_QUIET FALSE)
  if(package_name STREQUAL "cryptominisat")
    set(git_submodules_arg GIT_SUBMODULES)
  endif()
  cpmaddpackage(
    NAME
    ${package_name}
    DOWNLOAD_ONLY
    YES
    GITHUB_REPOSITORY
    ${repository}
    GIT_TAG
    ${git_tag}
    ${git_submodules_arg}
    GIT_PROGRESS
    TRUE)
  set(${out_var}
      "${${package_name}_SOURCE_DIR}"
      PARENT_SCOPE)
endfunction()

function(camada_prepare_cryptominisat_dependency_layout dependency_dir
         fetched_source_dir)
  if(EXISTS "${dependency_dir}" OR IS_SYMLINK "${dependency_dir}")
    file(REMOVE_RECURSE "${dependency_dir}")
  endif()

  execute_process(
    COMMAND ${CMAKE_COMMAND} -E create_symlink "${fetched_source_dir}"
            "${dependency_dir}"
    RESULT_VARIABLE symlink_result
    OUTPUT_QUIET ERROR_QUIET)
  if(NOT symlink_result EQUAL 0)
    file(COPY "${fetched_source_dir}" DESTINATION "${dependency_dir}/..")
    get_filename_component(dependency_name "${dependency_dir}" NAME)
    set(copied_dependency_dir "${dependency_dir}/../${dependency_name}")
    if(NOT copied_dependency_dir STREQUAL dependency_dir)
      file(RENAME "${copied_dependency_dir}" "${dependency_dir}")
    endif()
  endif()
endfunction()

# CMS 5.11.x finds CaDiCaL only as a sibling of its own source tree --
# find_library(cadical PATHS ../cadical/build/) -- and CadiBack compiles against
# ../cadical/src, so the sibling is a link to the shared source tree. CMS and
# the CadiBack commit pinned below use public CaDiCaL::Solver API only.
#
# ponytail: sibling-directory contract, because 5.11.22 has no cadical_DIR. The
# upgrade path is cadical_DIR, once a CMS release exists that does not need
# meelgroup's fork: 5.14.7 onward already have the variable, but also call
# CadiBack::doit() with arguments that need the fork's get_eqiv_lits.
function(camada_setup_cryptominisat_solver_deps cms_source_dir)
  get_filename_component(cms_parent_dir "${cms_source_dir}" DIRECTORY)
  set(cms_cadical_dir "${cms_parent_dir}/cadical")
  set(cms_cadiback_dir "${cms_parent_dir}/cadiback")

  # Above the guard, not inside it: the sibling link can already exist while the
  # archive it points at has been deleted, and the link line below names that
  # archive either way. The call is stamped, so a current build returns after
  # three EXISTS and a small read.
  camada_setup_shared_cadical()
  if(NOT EXISTS "${cms_cadical_dir}/build/libcadical.a")
    camada_prepare_cryptominisat_dependency_layout("${cms_cadical_dir}"
                                                   "${CAMADA_CADICAL_SRC_DIR}")
  endif()

  if(NOT EXISTS "${cms_cadiback_dir}/libcadiback.a")
    # The 'mate' branch CMS 5.11.22 documents no longer exists; this is the last
    # contemporary main commit whose CadiBack::doit() signature still matches
    # CMS 5.11.22's backbone.cpp (2024-06-07).
    camada_fetch_git_source(
      cryptominisat_cadiback meelgroup/cadiback
      69255f55e411207c4bdea02c6c2ab1ef29740ce1 cms_cadiback_source_dir)
    camada_prepare_cryptominisat_dependency_layout("${cms_cadiback_dir}"
                                                   "${cms_cadiback_source_dir}")
    camada_run_checked(
      WORKING_DIRECTORY
      "${cms_cadiback_dir}"
      MESSAGE
      "Configuring CryptoMiniSat CadiBack"
      COMMAND
      ${CMAKE_COMMAND}
      -E
      env
      "CXXFLAGS=-fPIC"
      ./configure)
    # cadiback ships a plain-text VERSION file holding "0.2.1". Apple Clang
    # searches the compilation directory for angle-bracket includes, so on a
    # case-insensitive filesystem the libc++ chain <algorithm> -> ... ->
    # <cstddef> -> #include <version> finds that file and the build dies on
    # "./version:1:1: expected unqualified-id". Swapping the implicit -I for
    # -iquote does not stop it.
    #
    # Only ./generate reads the file, and only to bake the string into
    # config.hpp, so generate that header first and then replace the contents
    # with a comment, which is valid C++ if anything does include it. The file
    # itself has to stay: make lists it as a prerequisite of config.hpp and
    # refuses to build when it is missing, timestamps notwithstanding.
    camada_run_checked(
      WORKING_DIRECTORY
      "${cms_cadiback_dir}"
      MESSAGE
      "Generating CryptoMiniSat CadiBack config"
      COMMAND
      make
      config.hpp)
    if(EXISTS "${cms_cadiback_dir}/VERSION")
      file(WRITE "${cms_cadiback_dir}/VERSION"
           "// Emptied by Camada once config.hpp captured the version.\n")
      # Rewriting VERSION makes it newer than config.hpp, which would send make
      # straight back through ./generate and bake this comment in as the version
      # string. Touch the header so the rule stays satisfied.
      file(TOUCH_NOCREATE "${cms_cadiback_dir}/config.hpp")
    endif()

    camada_run_checked(
      WORKING_DIRECTORY
      "${cms_cadiback_dir}"
      MESSAGE
      "Building CryptoMiniSat CadiBack"
      COMMAND
      make
      -j
      libcadiback.a)
  endif()
endfunction()

function(camada_setup_cryptominisat)
  set(cms_config
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cryptominisat5/cryptominisat5Config.cmake"
  )
  # Recipe stamp, same shape as CaDiCaL's and Yices': one stable filename
  # holding the recipe version, so a bump rebuilds rather than leaving an
  # orphaned stamp behind. Older installs built CMS against a private CaDiCaL
  # fork, so both it and CadiBack must be rebuilt against the shared one.
  set(cms_stamp
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cryptominisat5/camada-cms.stamp")
  set(cms_recipe_version "5.11.22:shared-cadical")
  camada_setup_shared_cadical()
  if(EXISTS "${cms_config}" AND EXISTS "${cms_stamp}")
    file(READ "${cms_stamp}" cms_stamp_contents)
    string(STRIP "${cms_stamp_contents}" cms_stamp_contents)
    if(cms_stamp_contents STREQUAL cms_recipe_version)
      return()
    endif()
  endif()

  camada_ensure_deps_dirs()
  file(
    REMOVE_RECURSE
    "${CMAKE_BINARY_DIR}/_deps/cryptominisat-src"
    "${CMAKE_BINARY_DIR}/_deps/cryptominisat-subbuild"
    "${CMAKE_BINARY_DIR}/_deps/cryptominisat_cadical-src"
    "${CMAKE_BINARY_DIR}/_deps/cryptominisat_cadical-subbuild"
    "${CMAKE_BINARY_DIR}/_deps/cryptominisat_cadiback-src"
    "${CMAKE_BINARY_DIR}/_deps/cryptominisat_cadiback-subbuild"
    "${CMAKE_BINARY_DIR}/_deps/cadical"
    "${CMAKE_BINARY_DIR}/_deps/cadiback")
  # 5.11.22 is the version STP 2.4.0 bumped its CI to (stp/stp#493).
  camada_fetch_git_source(cryptominisat msoos/cryptominisat 5.11.22
                          cms_source_dir)
  camada_setup_cryptominisat_solver_deps("${cms_source_dir}")
  get_filename_component(cms_parent_dir "${cms_source_dir}" DIRECTORY)

  set(cms_build_dir "${cms_source_dir}/build")
  file(REMOVE_RECURSE "${cms_build_dir}")
  file(MAKE_DIRECTORY "${cms_build_dir}")

  camada_run_checked(
    WORKING_DIRECTORY
    "${cms_build_dir}"
    MESSAGE
    "Configuring CryptoMiniSat"
    COMMAND
    ${CMAKE_COMMAND}
    ..
    -GNinja
    -DENABLE_ASSERTIONS=OFF
    -DBUILD_SHARED_LIBS=OFF
    -DNOZLIB=ON
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5
    -DCMAKE_BUILD_TYPE=Release
    # Pin the flags empty rather than inherit CXXFLAGS from the environment:
    # CadiBack's configure hardcodes its own compile line, so a flag that
    # changes mangling (-D_GLIBCXX_DEBUG, -stdlib=libc++) would reach CMS and
    # not CadiBack, and the two would fail to link together.
    -DCMAKE_CXX_FLAGS=
    -DCMAKE_INSTALL_PREFIX=${CAMADA_DEPS_INSTALL_DIR})
  camada_run_checked(WORKING_DIRECTORY "${cms_build_dir}" MESSAGE
                     "Building CryptoMiniSat" COMMAND ninja)
  camada_run_checked(
    WORKING_DIRECTORY
    "${cms_build_dir}"
    MESSAGE
    "Installing CryptoMiniSat"
    COMMAND
    ninja
    install)

  set(cms_cadiback_lib "${cms_parent_dir}/cadiback/libcadiback.a")
  # Every consumer links the one shared CaDiCaL; only CadiBack is staged, and
  # FindSTP.cmake links it after libcryptominisat5.a.
  file(COPY_FILE "${cms_cadiback_lib}"
       "${CAMADA_DEPS_INSTALL_DIR}/lib/libcadiback.a")
  file(
    APPEND "${cms_config}"
    "\nset(CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS \"${CAMADA_DEPS_INSTALL_DIR}/lib/libcadiback.a;${CAMADA_CADICAL_LIB}\")\n"
  )

  # CMS's install exports cadical/cadiback CMake packages whose archives are
  # never installed, and hardcodes their absolute build-tree paths in the
  # cryptominisat5 export; STP's find_package trips over both. The staged
  # CadiBack and the shared CaDiCaL replace them, so scrub the references.
  file(REMOVE_RECURSE "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cadiback"
       "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cadical")
  set(cms_targets_file
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cryptominisat5/cryptominisat5Targets.cmake"
  )
  file(READ "${cms_targets_file}" cms_targets_contents)
  string(REGEX REPLACE ";?[^;\"]*libcadi(back|cal)\\.a" "" cms_targets_contents
                       "${cms_targets_contents}")
  file(WRITE "${cms_targets_file}" "${cms_targets_contents}")

  file(REMOVE "${CAMADA_DEPS_INSTALL_DIR}/lib/libcadical-cms.a")
  file(WRITE "${cms_stamp}" "${cms_recipe_version}\n")
endfunction()

function(camada_setup_gmp)
  set(gmp_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libgmp.a")
  set(gmp_header "${CAMADA_DEPS_INSTALL_DIR}/include/gmp.h")
  if(EXISTS "${gmp_lib}" AND EXISTS "${gmp_header}")
    return()
  endif()

  camada_find_gmp_header(_camada_system_gmp_include_dir)
  if(EXISTS "${gmp_lib}"
     AND NOT EXISTS "${gmp_header}"
     AND _camada_system_gmp_include_dir)
    file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/include")
    execute_process(
      COMMAND ${CMAKE_COMMAND} -E create_symlink
              "${_camada_system_gmp_include_dir}/gmp.h" "${gmp_header}")
    return()
  endif()

  camada_ensure_deps_dirs()
  camada_fetch_git_source(gmp gmp-mirror/gmp 141ed4f98a50 gmp_source_dir)

  camada_run_checked(
    WORKING_DIRECTORY
    "${gmp_source_dir}"
    MESSAGE
    "Preparing GMP"
    COMMAND
    autoreconf
    -fi)
  camada_run_checked(
    WORKING_DIRECTORY
    "${gmp_source_dir}"
    MESSAGE
    "Configuring GMP"
    COMMAND
    ./configure
    --prefix=${CAMADA_DEPS_INSTALL_DIR}
    --disable-shared
    ABI=64
    # -std=gnu17: GCC 14 defaults to C23, where GMP's own "long long
    # reliability" probe no longer compiles -- it declares `void g(){}` and then
    # calls it with six arguments, which C23 rejects outright. Every compiler
    # probe then fails and configure stops with "could not find a working
    # compiler", so a host without a system GMP could not build any backend that
    # needs one.
    CFLAGS=-fPIC\ -std=gnu17
    CPPFLAGS=-DPIC)
  camada_run_checked(
    WORKING_DIRECTORY
    "${gmp_source_dir}/doc"
    MESSAGE
    "Preparing GMP docs"
    COMMAND
    make
    stamp-vti)
  camada_run_checked(
    WORKING_DIRECTORY
    "${gmp_source_dir}"
    MESSAGE
    "Building GMP"
    COMMAND
    make
    -j)
  camada_run_checked(
    WORKING_DIRECTORY
    "${gmp_source_dir}"
    MESSAGE
    "Installing GMP"
    COMMAND
    make
    install)

  camada_find_gmp_header(_camada_system_gmp_include_dir)
  if(NOT EXISTS "${gmp_header}" AND _camada_system_gmp_include_dir)
    file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/include")
    execute_process(
      COMMAND ${CMAKE_COMMAND} -E create_symlink
              "${_camada_system_gmp_include_dir}/gmp.h" "${gmp_header}")
  endif()
endfunction()

function(camada_setup_minisat)
  set(minisat_config
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/minisat/minisatConfig.cmake")
  set(minisat_source_stamp
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/minisat/camada-source-build.stamp")
  if(EXISTS "${minisat_config}" AND EXISTS "${minisat_source_stamp}")
    return()
  endif()

  camada_ensure_deps_dirs()
  camada_fetch_git_source(minisat msoos/minisat 2.2.1 minisat_source_dir)
  set(minisat_prefix "${CAMADA_DEPS_INSTALL_DIR}")

  if(APPLE)
    set(minisat_system_cc "${minisat_source_dir}/minisat/utils/System.cc")
    if(EXISTS "${minisat_system_cc}")
      file(READ "${minisat_system_cc}" minisat_system_cc_contents)
      string(
        REPLACE
          "double Minisat::memUsedPeak() { return memUsed(); }"
          "double Minisat::memUsedPeak(bool strictlyPeak) { (void)strictlyPeak; return memUsed(); }"
          minisat_system_cc_contents
          "${minisat_system_cc_contents}")
      file(WRITE "${minisat_system_cc}" "${minisat_system_cc_contents}")
    endif()
  endif()

  camada_run_checked(
    WORKING_DIRECTORY
    "${minisat_source_dir}"
    MESSAGE
    "Configuring Minisat"
    COMMAND
    make
    config
    BUILD_DIR=build
    prefix=${minisat_prefix})
  camada_run_checked(
    WORKING_DIRECTORY
    "${minisat_source_dir}"
    MESSAGE
    "Building Minisat"
    COMMAND
    make
    -j
    CXXFLAGS=-fPIC
    build/release/lib/libminisat.a)

  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/lib")
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/include")
  file(COPY "${minisat_source_dir}/build/release/lib/libminisat.a"
       DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/lib")
  file(COPY "${minisat_source_dir}/minisat"
       DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/include")

  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/minisat")
  file(
    WRITE "${minisat_config}"
    "if(NOT TARGET minisat)\n  add_library(minisat STATIC IMPORTED)\n  set_target_properties(minisat PROPERTIES IMPORTED_LOCATION \"${CAMADA_DEPS_INSTALL_DIR}/lib/libminisat.a\" INTERFACE_INCLUDE_DIRECTORIES \"${CAMADA_DEPS_INSTALL_DIR}/include\")\nendif()\n"
  )
  file(WRITE "${minisat_source_stamp}" "1\n")
endfunction()

# Builds the CaDiCaL that both Bitwuzla and CVC5 link against, with the same
# source and flags CVC5's own recipe uses (cmake/FindCaDiCaL.cmake). -DQUIET in
# particular is load-bearing: it changes CaDiCaL::Internal's layout, so a
# CaDiCaL built without it is not interchangeable with CVC5's.
function(camada_setup_shared_cadical)
  set(cadical_prefix "${CAMADA_CADICAL_PREFIX}")
  set(cadical_lib "${CAMADA_CADICAL_LIB}")
  set(cadical_header "${cadical_prefix}/include/cadical/cadical.hpp")
  set(cadical_stamp "${cadical_prefix}/camada-cadical.stamp")
  # Bump when the URL or the flags below change, so an install left by an older
  # recipe is rebuilt rather than silently reused.
  set(cadical_recipe_version "3:${CAMADA_CADICAL_SHA256}")

  if(EXISTS "${cadical_lib}" AND EXISTS "${cadical_header}")
    if(EXISTS "${cadical_stamp}")
      file(READ "${cadical_stamp}" cadical_stamp_contents)
      string(STRIP "${cadical_stamp_contents}" cadical_stamp_contents)
      if(cadical_stamp_contents STREQUAL cadical_recipe_version)
        return()
      endif()
    endif()
  endif()

  camada_ensure_deps_dirs()
  get_filename_component(cadical_archive_name "${CAMADA_CADICAL_URL}" NAME)
  set(cadical_archive "${CAMADA_DEPS_SRC_DIR}/${cadical_archive_name}")

  camada_download_file("${CAMADA_CADICAL_URL}" "${cadical_archive}")
  file(SHA256 "${cadical_archive}" cadical_actual_sha256)
  if(NOT cadical_actual_sha256 STREQUAL CAMADA_CADICAL_SHA256)
    message(
      FATAL_ERROR
        "CaDiCaL archive checksum mismatch.\nURL: ${CAMADA_CADICAL_URL}\nExpected: ${CAMADA_CADICAL_SHA256}\nActual:   ${cadical_actual_sha256}"
    )
  endif()

  # cmake -E tar cannot strip a leading component, so extract into the
  # cadical-<tag>/ directory the archive carries.
  set(cadical_source_dir "${CAMADA_CADICAL_SRC_DIR}")
  camada_extract_archive(
    ARCHIVE_PATH
    "${cadical_archive}"
    DESTINATION_DIR
    "${CAMADA_DEPS_SRC_DIR}"
    MARKER_PATH
    "${cadical_source_dir}/makefile.in"
    ARCHIVE_URL
    "${CAMADA_CADICAL_URL}"
    SOURCE_DIR
    "${cadical_source_dir}")

  # CVC5's flags, including the same feature probes: CaDiCaL guards these calls
  # on the macros instead of detecting them, so a platform without closefrom()
  # (macOS) fails to compile without -DNCLOSEFROM. -DQUIET is the load-bearing
  # one for ABI compatibility and is not conditional. check_cxx_symbol_exists,
  # not check_symbol_exists: Camada enables C as well as C++, so the plain form
  # compiles the probe as C, where <cstdio> does not exist and every probe
  # fails. CaDiCaL is C++, so ask the C++ compiler.
  include(CheckCXXSymbolExists)
  set(cadical_cxxflags "-fPIC -O3 -DNDEBUG -DQUIET -std=c++11")
  check_cxx_symbol_exists("getc_unlocked" "cstdio"
                          CAMADA_CADICAL_HAVE_UNLOCKED_IO)
  if(NOT CAMADA_CADICAL_HAVE_UNLOCKED_IO)
    string(APPEND cadical_cxxflags " -DNUNLOCKED")
  endif()
  check_cxx_symbol_exists("closefrom" "fcntl.h" CAMADA_CADICAL_HAVE_CLOSEFROM)
  if(NOT CAMADA_CADICAL_HAVE_CLOSEFROM)
    string(APPEND cadical_cxxflags " -DNCLOSEFROM")
  endif()
  # macOS headers are not necessarily under /usr/include any more.
  if(CMAKE_OSX_SYSROOT)
    string(APPEND cadical_cxxflags
           " ${CMAKE_CXX_SYSROOT_FLAG} ${CMAKE_OSX_SYSROOT}")
  endif()

  # CaDiCaL's configure script is avoided the same way CVC5 avoids it: the
  # makefile template is instantiated directly, which also keeps the flags under
  # our control rather than the script's.
  set(cadical_build_dir "${cadical_source_dir}/build")
  file(MAKE_DIRECTORY "${cadical_build_dir}")
  file(READ "${cadical_source_dir}/makefile.in" cadical_makefile)
  string(REPLACE "@CXX@" "${CMAKE_CXX_COMPILER}" cadical_makefile
                 "${cadical_makefile}")
  string(REPLACE "@CXXFLAGS@" "${cadical_cxxflags}" cadical_makefile
                 "${cadical_makefile}")
  string(REPLACE "@ROOT@" "${cadical_source_dir}" cadical_makefile
                 "${cadical_makefile}")
  string(REPLACE "@CONTRIB@" "no" cadical_makefile "${cadical_makefile}")
  file(WRITE "${cadical_build_dir}/makefile" "${cadical_makefile}")

  camada_run_checked(
    WORKING_DIRECTORY
    "${cadical_build_dir}"
    MESSAGE
    "Building CaDiCaL"
    COMMAND
    make
    -j
    libcadical.a)

  file(MAKE_DIRECTORY "${cadical_prefix}/lib")
  file(MAKE_DIRECTORY "${cadical_prefix}/include/cadical")
  file(COPY "${cadical_build_dir}/libcadical.a"
       DESTINATION "${cadical_prefix}/lib")
  file(COPY "${cadical_source_dir}/src/cadical.hpp"
            "${cadical_source_dir}/src/tracer.hpp"
       DESTINATION "${cadical_prefix}/include/cadical")
  file(WRITE "${cadical_stamp}" "${cadical_recipe_version}\n")
endfunction()

# Builds Bitwuzla from source against the shared CaDiCaL. Bitwuzla's
# src/meson.build prefers a system CaDiCaL over its bundled subproject:
# cadical_dep = cpp_compiler.find_library('cadical', has_headers: [...]) so
# staging the shared build where the compiler looks is enough to keep the stock
# copy out of libbitwuzla.a. find_library consults the compiler's own search
# path, which -Dcpp_link_args does not extend -- hence LIBRARY_PATH.
function(camada_build_bitwuzla_from_source cadical_prefix)
  camada_find_program_with_prefixes(meson_program meson)
  camada_find_program_with_prefixes(ninja_program ninja)
  if(NOT meson_program OR NOT ninja_program)
    message(
      FATAL_ERROR
        "Building Bitwuzla from source needs meson and ninja on PATH. Camada builds it from source whenever the Bitwuzla and CVC5 backends are both enabled, so that they share one CaDiCaL; install them, or disable one of the two backends."
    )
  endif()

  camada_fetch_git_source(bitwuzla bitwuzla/bitwuzla
                          "${CAMADA_BITWUZLA_GIT_TAG}" bitwuzla_source_dir)
  set(bitwuzla_build_dir "${bitwuzla_source_dir}/build-camada")
  file(REMOVE_RECURSE "${bitwuzla_build_dir}")

  set(saved_library_path "$ENV{LIBRARY_PATH}")
  set(saved_cpath "$ENV{CPATH}")
  if(saved_library_path)
    set(ENV{LIBRARY_PATH} "${cadical_prefix}/lib:${saved_library_path}")
  else()
    set(ENV{LIBRARY_PATH} "${cadical_prefix}/lib")
  endif()
  if(saved_cpath)
    set(ENV{CPATH} "${cadical_prefix}/include:${saved_cpath}")
  else()
    set(ENV{CPATH} "${cadical_prefix}/include")
  endif()

  camada_run_checked(
    WORKING_DIRECTORY
    "${bitwuzla_source_dir}"
    MESSAGE
    "Configuring Bitwuzla against the shared CaDiCaL"
    COMMAND
    "${meson_program}"
    setup
    "${bitwuzla_build_dir}"
    "--prefix=${CAMADA_DEPS_INSTALL_DIR}"
    "--default-library=static"
    "--buildtype=release"
    -Dcadical=true
    -Dkissat=false
    -Dcryptominisat=false
    -Dgimsatul=false
    -Dtesting=disabled)
  camada_run_checked(WORKING_DIRECTORY "${bitwuzla_build_dir}" MESSAGE
                     "Building Bitwuzla" COMMAND "${ninja_program}")
  # Meson may install into a different libdir than the old prebuilt. Remove its
  # archives and pkg-config files so discovery cannot select that copy.
  file(
    GLOB
    bitwuzla_old_files
    "${CAMADA_DEPS_INSTALL_DIR}/lib/libbitwuzla*.a"
    "${CAMADA_DEPS_INSTALL_DIR}/lib/*/libbitwuzla*.a"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/libbitwuzla*.a"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/*/libbitwuzla*.a"
    "${CAMADA_DEPS_INSTALL_DIR}/lib/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib/*/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/*/pkgconfig/bitwuzla.pc")
  if(bitwuzla_old_files)
    file(REMOVE ${bitwuzla_old_files})
  endif()
  camada_run_checked(
    WORKING_DIRECTORY
    "${bitwuzla_build_dir}"
    MESSAGE
    "Installing Bitwuzla"
    COMMAND
    "${ninja_program}"
    install)

  set(ENV{LIBRARY_PATH} "${saved_library_path}")
  set(ENV{CPATH} "${saved_cpath}")
endfunction()

# Always from source, against the shared CaDiCaL. Bitwuzla's prebuilt archive
# bundles its own CaDiCaL, which would be a second copy in any build that also
# enables CVC5 or STP.
function(camada_setup_bitwuzla)
  set(bitwuzla_stamp
      "${CAMADA_DEPS_INSTALL_DIR}/include/bitwuzla/camada-bitwuzla.stamp")
  set(bitwuzla_recipe_version "${CAMADA_BITWUZLA_GIT_TAG}:shared-cadical")
  set(bitwuzla_stamp_current FALSE)
  if(EXISTS "${bitwuzla_stamp}")
    file(READ "${bitwuzla_stamp}" bitwuzla_stamp_contents)
    string(STRIP "${bitwuzla_stamp_contents}" bitwuzla_stamp_contents)
    if(bitwuzla_stamp_contents STREQUAL bitwuzla_recipe_version)
      set(bitwuzla_stamp_current TRUE)
    endif()
  endif()
  camada_setup_shared_cadical()
  if(NOT EXISTS "${CAMADA_DEPS_INSTALL_DIR}/include/bitwuzla/c/bitwuzla.h"
     OR NOT bitwuzla_stamp_current)
    camada_ensure_deps_dirs()
    camada_build_bitwuzla_from_source("${CAMADA_CADICAL_PREFIX}")
    file(WRITE "${bitwuzla_stamp}" "${bitwuzla_recipe_version}\n")
  endif()

  # Bitwuzla is built against the shared CaDiCaL, so the pkg-config file has to
  # name it; meson writes its own absolute build-time path, which this rewrite
  # replaces.
  #
  # As -L/-l rather than an absolute path: pkg-config sorts an absolute .a into
  # LDFLAGS_OTHER instead of LINK_LIBRARIES, and CMake then applies it to
  # whichever target happens to consume the raw flags rather than to everything
  # that links Bitwuzla. camada-regression picked it up and camada-bench did
  # not, so a Bitwuzla-only build failed on undefined CaDiCaL::Solver symbols.
  set(bitwuzla_cadical_flags " -L${CAMADA_CADICAL_PREFIX}/lib -lcadical")

  file(
    GLOB
    bitwuzla_pc_files
    "${CAMADA_DEPS_INSTALL_DIR}/lib/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib/*/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/*/pkgconfig/bitwuzla.pc")
  foreach(bitwuzla_pc_file IN LISTS bitwuzla_pc_files)
    get_filename_component(bitwuzla_pkgconfig_dir "${bitwuzla_pc_file}"
                           DIRECTORY)
    get_filename_component(bitwuzla_libdir "${bitwuzla_pkgconfig_dir}"
                           DIRECTORY)
    file(
      WRITE "${bitwuzla_pc_file}"
      "prefix=${CAMADA_DEPS_INSTALL_DIR}\nincludedir=\${prefix}/include\nlibdir=${bitwuzla_libdir}\n\nName: bitwuzla\nDescription: bitwuzla: bitwuzla\nVersion: 0.9.1\nRequires: gmp >= 6.3, mpfr >= 4.2.1\nLibs: -L\${libdir} -lbitwuzla -lbitwuzlals -lbitwuzlabv -lbitwuzlabb${bitwuzla_cadical_flags}\nCflags: -I\${includedir}\n"
    )
  endforeach()
endfunction()

# CVC5's prebuilt ships its own libcadical.a and its exported targets name it by
# bare name, so -lcadical resolves to the staged copy. When Bitwuzla was built
# from source against the shared CaDiCaL, that leaves two exported CaDiCaLs in
# one binary -- the arrangement this mechanism exists to prevent. Both are the
# same source built with the same flags, so point CVC5 at the shared archive and
# drop the redundant copy.
#
# Called from both paths through camada_setup_cvc5: a restored dependency cache
# returns before staging ever runs, and a tree cached before this fix still
# holds CVC5's copy. Idempotent, so running it on every configure is the point
# rather than a cost.
function(camada_point_cvc5_at_shared_cadical)
  set(cvc5_targets_file
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cvc5/cvc5Targets.cmake")
  if(NOT EXISTS "${cvc5_targets_file}")
    return()
  endif()
  # This runs on every configure, so do nothing unless the export still names
  # the bare `cadical`: an already-patched tree costs one read. Otherwise build
  # the shared CaDiCaL if nothing has yet -- CVC5 can be the only backend
  # enabled, in which case no other setup function has run.
  camada_setup_shared_cadical()
  file(READ "${cvc5_targets_file}" cvc5_targets_contents)
  string(FIND "${cvc5_targets_contents}" "LINK_ONLY:cadical>" cvc5_bare_cadical)
  if(cvc5_bare_cadical EQUAL -1)
    return()
  endif()
  string(REPLACE "LINK_ONLY:cadical>" "LINK_ONLY:${CAMADA_CADICAL_LIB}>"
                 cvc5_targets_contents "${cvc5_targets_contents}")
  file(WRITE "${cvc5_targets_file}" "${cvc5_targets_contents}")
  file(REMOVE "${CAMADA_DEPS_INSTALL_DIR}/lib/libcadical.a")
endfunction()

function(camada_setup_cvc5)
  set(cvc5_config "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cvc5/cvc5Config.cmake")
  if(EXISTS "${cvc5_config}")
    file(READ "${cvc5_config}" cvc5_config_contents)
    string(REPLACE "set(CVC5_BINDINGS_JAVA ON)" "set(CVC5_BINDINGS_JAVA OFF)"
                   cvc5_config_contents "${cvc5_config_contents}")
    file(WRITE "${cvc5_config}" "${cvc5_config_contents}")
    camada_point_cvc5_at_shared_cadical()
    return()
  endif()

  camada_ensure_deps_dirs()
  camada_select_prebuilt_url(cvc5_url CVC5)

  get_filename_component(cvc5_archive_name "${cvc5_url}" NAME)
  string(REGEX REPLACE "\\.zip$" "" cvc5_root_dir_name "${cvc5_archive_name}")
  set(cvc5_archive "${CAMADA_DEPS_SRC_DIR}/${cvc5_archive_name}")
  set(cvc5_root_dir "${CAMADA_DEPS_SRC_DIR}/${cvc5_root_dir_name}")

  camada_download_file("${cvc5_url}" "${cvc5_archive}")
  camada_extract_archive(
    ARCHIVE_PATH
    "${cvc5_archive}"
    DESTINATION_DIR
    "${CAMADA_DEPS_SRC_DIR}"
    MARKER_PATH
    "${cvc5_root_dir}"
    ARCHIVE_URL
    "${cvc5_url}"
    SOURCE_DIR
    "${cvc5_root_dir}")
  camada_stage_prebuilt_tree("${cvc5_root_dir}")

  camada_point_cvc5_at_shared_cadical()
  file(READ "${cvc5_config}" cvc5_config_contents)
  string(REPLACE "set(CVC5_BINDINGS_JAVA ON)" "set(CVC5_BINDINGS_JAVA OFF)"
                 cvc5_config_contents "${cvc5_config_contents}")
  file(WRITE "${cvc5_config}" "${cvc5_config_contents}")
endfunction()

function(camada_setup_stp)
  camada_setup_cryptominisat()
  set(stp_config "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/STP/STPConfig.cmake")
  # libabc-pic.a is staged by this function for STP >= 2.4.0 only, so its
  # presence also distinguishes a current install from a stale 2.3.x one left
  # behind in an existing build directory.
  if(EXISTS "${stp_config}" AND EXISTS
                                "${CAMADA_DEPS_INSTALL_DIR}/lib/libabc-pic.a")
    return()
  endif()

  message(
    STATUS
      "The STP 2.4.1 GitHub release asset is a standalone solver binary, not a development package with headers and libraries. Falling back to a source build for Camada's STP API wrapper."
  )

  camada_setup_minisat()
  camada_fetch_git_source(stpsrc stp/stp 2.4.1 stp_source_dir)
  if(APPLE)
    file(READ "${stp_source_dir}/CMakeLists.txt" stp_cmake_contents)
    string(
      REPLACE
        "        set(CMAKE_EXE_LINKER_FLAGS \"\${CMAKE_EXE_LINKER_FLAGS} -static -Wl,--whole-archive -lpthread -Wl,--no-whole-archive -static \")"
        ""
        stp_cmake_contents
        "${stp_cmake_contents}")
    file(WRITE "${stp_source_dir}/CMakeLists.txt" "${stp_cmake_contents}")
  endif()

  set(stp_build_dir "${stp_source_dir}/build")
  set(cms_config_dir "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cryptominisat5")
  camada_find_program_with_prefixes(stp_bison_executable bison)
  camada_find_program_with_prefixes(stp_flex_executable flex)
  file(REMOVE_RECURSE "${stp_build_dir}")
  file(MAKE_DIRECTORY "${stp_build_dir}")

  set(_camada_stp_cmake_args
      ..
      -GNinja
      -DONLY_SIMPLE=ON
      -DCMAKE_INSTALL_PREFIX=${CAMADA_DEPS_INSTALL_DIR}
      -DCMAKE_BUILD_TYPE=Release
      -DCMAKE_CXX_FLAGS=-DABC_USE_STDINT_H=1
      # The stp binary doubles as an SMT-LIB pipeline child in the regression
      # suite.
      -DBUILD_EXECUTABLES=ON
      -DSTATICCOMPILE=ON
      -DBUILD_SHARED_LIBS=OFF
      -Dminisat_DIR=${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/minisat
      # STP's Findminisat.cmake module ignores minisat_DIR; without these hints
      # it can resolve a system minisat whose headers and ABI differ from the
      # staged one.
      -DMINISAT_INCLUDE_DIRS=${CAMADA_DEPS_INSTALL_DIR}/include
      -DMINISAT_LIBDIR=${CAMADA_DEPS_INSTALL_DIR}/lib
      -Dcryptominisat5_DIR=${cms_config_dir})
  if(APPLE)
    list(APPEND _camada_stp_cmake_args -DHAVE_UNISTD_H=ON)
  endif()
  if(stp_bison_executable)
    list(APPEND _camada_stp_cmake_args
         -DBISON_EXECUTABLE=${stp_bison_executable})
  endif()
  if(stp_flex_executable)
    list(APPEND _camada_stp_cmake_args -DFLEX_EXECUTABLE=${stp_flex_executable})
  endif()
  camada_run_checked(
    WORKING_DIRECTORY
    "${stp_build_dir}"
    MESSAGE
    "Configuring STP"
    COMMAND
    ${CMAKE_COMMAND}
    ${_camada_stp_cmake_args})
  camada_run_checked(WORKING_DIRECTORY "${stp_build_dir}" MESSAGE
                     "Building STP" COMMAND ninja)
  camada_run_checked(
    WORKING_DIRECTORY
    "${stp_build_dir}"
    MESSAGE
    "Installing STP"
    COMMAND
    ninja
    install)

  # STP >= 2.4.0 builds ABC as a separate static archive that its exported
  # target references from the build tree but never installs; stage it next to
  # libstp.a so FindSTP.cmake can link it.
  file(COPY "${stp_build_dir}/lib/libabc-pic.a"
       DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/lib")
endfunction()

function(camada_setup_yices)
  set(yices_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libyices.a")
  set(yices_header "${CAMADA_DEPS_INSTALL_DIR}/include/yices.h")
  set(yices_shared_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libyices.so")
  set(yices_shared_soname "${CAMADA_DEPS_INSTALL_DIR}/lib/libyices.so.2.7.0")
  set(yices_source_stamp
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/yices/camada-source-build.stamp")
  # Bump when the configure flags below change, so an install left by an older
  # recipe is rebuilt rather than silently reused: the stamp used to record only
  # that a source build had happened, not which one.
  set(yices_recipe_version "1")
  set(yices_stamp_current FALSE)
  if(EXISTS "${yices_source_stamp}")
    file(READ "${yices_source_stamp}" yices_stamp_contents)
    string(STRIP "${yices_stamp_contents}" yices_stamp_contents)
    if(yices_stamp_contents STREQUAL yices_recipe_version)
      set(yices_stamp_current TRUE)
    endif()
  endif()
  if(BUILD_SHARED_LIBS
     AND EXISTS "${yices_shared_lib}"
     AND EXISTS "${yices_header}"
     AND yices_stamp_current)
    return()
  endif()
  if(NOT BUILD_SHARED_LIBS
     AND EXISTS "${yices_lib}"
     AND EXISTS "${yices_header}"
     AND yices_stamp_current)
    if(EXISTS "${yices_shared_soname}" AND NOT EXISTS "${yices_shared_lib}")
      file(CREATE_LINK "${yices_shared_soname}" "${yices_shared_lib}" SYMBOLIC)
    endif()
    return()
  endif()

  camada_ensure_deps_dirs()
  if(NOT BUILD_SHARED_LIBS)
    message(
      STATUS
        "Using a Yices source build for static Camada builds because the upstream prebuilt archive does not provide complete link dependency metadata."
    )
  else()
    message(
      STATUS
        "Using a Yices source build because Camada requires a Yices library with complete transitive dependencies."
    )
  endif()

  camada_setup_gmp()
  camada_fetch_git_source(yices2 SRI-CSL/yices2 yices-2.7.0 yices_source_dir)
  camada_run_checked(WORKING_DIRECTORY "${yices_source_dir}" MESSAGE
                     "Preparing Yices" COMMAND autoreconf)
  camada_run_checked(
    WORKING_DIRECTORY
    "${yices_source_dir}"
    MESSAGE
    "Configuring Yices"
    COMMAND
    ./configure
    --prefix
    ${CAMADA_DEPS_INSTALL_DIR}
    --with-static-gmp=${CAMADA_DEPS_INSTALL_DIR}/lib/libgmp.a
    CPPFLAGS=-I${CAMADA_DEPS_INSTALL_DIR}/include
    LDFLAGS=-L${CAMADA_DEPS_INSTALL_DIR}/lib/)
  camada_run_checked(
    WORKING_DIRECTORY
    "${yices_source_dir}"
    MESSAGE
    "Building Yices"
    COMMAND
    make
    -j)
  camada_run_checked(
    WORKING_DIRECTORY
    "${yices_source_dir}"
    MESSAGE
    "Building Yices static library"
    COMMAND
    make
    static-lib)
  camada_run_checked(
    WORKING_DIRECTORY
    "${yices_source_dir}"
    MESSAGE
    "Installing Yices"
    COMMAND
    make
    install)
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/yices")
  file(WRITE "${yices_source_stamp}" "${yices_recipe_version}\n")
endfunction()

function(camada_setup_z3)
  set(z3_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libz3.a")
  if(BUILD_SHARED_LIBS)
    set(z3_lib
        "${CAMADA_DEPS_INSTALL_DIR}/bin/libz3${CMAKE_SHARED_LIBRARY_SUFFIX}")
  endif()
  if(EXISTS "${z3_lib}" OR EXISTS "${CAMADA_DEPS_INSTALL_DIR}/include/z3.h")
    return()
  endif()

  camada_ensure_deps_dirs()
  camada_select_prebuilt_url(z3_url Z3)

  get_filename_component(z3_archive_name "${z3_url}" NAME)
  string(REGEX REPLACE "\\.zip$" "" z3_root_dir_name "${z3_archive_name}")
  set(z3_archive "${CAMADA_DEPS_SRC_DIR}/${z3_archive_name}")
  set(z3_root_dir "${CAMADA_DEPS_SRC_DIR}/${z3_root_dir_name}")

  camada_download_file("${z3_url}" "${z3_archive}")
  camada_extract_archive(
    ARCHIVE_PATH
    "${z3_archive}"
    DESTINATION_DIR
    "${CAMADA_DEPS_SRC_DIR}"
    MARKER_PATH
    "${z3_root_dir}"
    ARCHIVE_URL
    "${z3_url}"
    SOURCE_DIR
    "${z3_root_dir}")
  camada_stage_prebuilt_tree("${z3_root_dir}")

  if(APPLE)
    set(z3_shared_lib
        "${CAMADA_DEPS_INSTALL_DIR}/bin/libz3${CMAKE_SHARED_LIBRARY_SUFFIX}")
    if(EXISTS "${z3_shared_lib}")
      execute_process(
        COMMAND install_name_tool -id
                "@rpath/libz3${CMAKE_SHARED_LIBRARY_SUFFIX}" "${z3_shared_lib}"
        RESULT_VARIABLE z3_install_name_result
        OUTPUT_VARIABLE z3_install_name_stdout
        ERROR_VARIABLE z3_install_name_stderr)
      if(NOT z3_install_name_result EQUAL 0)
        message(
          FATAL_ERROR
            "Failed to normalize the Z3 install name for ${z3_shared_lib}\nstdout:\n${z3_install_name_stdout}\nstderr:\n${z3_install_name_stderr}"
        )
      endif()
    endif()
  endif()
endfunction()

# Stage the macOS MathSAT binary into ${CAMADA_DEPS_INSTALL_DIR}/bin and rewrite
# its hard-coded /opt/local/lib/libgmp.10.dylib LC_LOAD_DYLIB so the binary can
# launch on machines that don't ship MacPorts. The vendor archive's prebuilt
# binary always points at the MacPorts GMP path; on Homebrew hosts dyld aborts
# the process before it reads any input, which breaks every SMTLIB pipeline test
# for MathSAT. We rewrite the path to whichever libgmp.10.dylib we can locate
# (Homebrew first, then a few well-known prefixes) and ad-hoc resign because
# arm64 rejects a modified binary that still carries its old signature. If no
# usable dylib is found we leave the binary alone — a MacPorts host already
# satisfies the original load path, and any other host will have its pipeline
# tests SKIP because the binary will fail to launch.
function(camada_stage_macos_mathsat_binary mathsat_source_dir)
  set(src_binary "${mathsat_source_dir}/bin/mathsat")
  if(NOT EXISTS "${src_binary}")
    return()
  endif()

  set(dst_binary "${CAMADA_DEPS_INSTALL_DIR}/bin/mathsat")
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/bin")
  file(COPY "${src_binary}" DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/bin")

  set(_gmp_candidates "")
  find_program(_camada_brew brew)
  if(_camada_brew)
    execute_process(
      COMMAND "${_camada_brew}" --prefix gmp
      OUTPUT_VARIABLE _brew_gmp_prefix
      OUTPUT_STRIP_TRAILING_WHITESPACE
      RESULT_VARIABLE _brew_gmp_rc
      ERROR_QUIET)
    if(_brew_gmp_rc EQUAL 0 AND _brew_gmp_prefix)
      list(APPEND _gmp_candidates "${_brew_gmp_prefix}/lib/libgmp.10.dylib")
    endif()
  endif()
  list(
    APPEND
    _gmp_candidates
    "/opt/homebrew/opt/gmp/lib/libgmp.10.dylib"
    "/opt/homebrew/lib/libgmp.10.dylib"
    "/usr/local/opt/gmp/lib/libgmp.10.dylib"
    "/usr/local/lib/libgmp.10.dylib"
    "/opt/local/lib/libgmp.10.dylib")

  set(_gmp_dylib "")
  foreach(candidate IN LISTS _gmp_candidates)
    if(EXISTS "${candidate}")
      set(_gmp_dylib "${candidate}")
      break()
    endif()
  endforeach()

  if(NOT _gmp_dylib)
    message(
      STATUS
        "MathSAT: no libgmp.10.dylib found on host; SMTLIB pipeline tests will SKIP."
    )
    return()
  endif()

  if(_gmp_dylib STREQUAL "/opt/local/lib/libgmp.10.dylib")
    return()
  endif()

  execute_process(
    COMMAND install_name_tool -change /opt/local/lib/libgmp.10.dylib
            "${_gmp_dylib}" "${dst_binary}" RESULT_VARIABLE _rc)
  if(NOT _rc EQUAL 0)
    message(
      WARNING "MathSAT: install_name_tool failed (${_rc}) on ${dst_binary}")
    return()
  endif()
  execute_process(COMMAND codesign --force --sign - "${dst_binary}"
                  RESULT_VARIABLE _rc)
  if(NOT _rc EQUAL 0)
    message(WARNING "MathSAT: codesign failed (${_rc}) on ${dst_binary}")
  endif()
endfunction()

function(camada_setup_mathsat)
  set(mathsat_header "${CAMADA_DEPS_INSTALL_DIR}/include/mathsat.h")
  if(EXISTS "${mathsat_header}")
    if(CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
      camada_select_mathsat_prebuilt_info(_unused_url _unused_archive
                                          _cached_source_dir)
      camada_stage_macos_mathsat_binary("${_cached_source_dir}")
    endif()
    return()
  endif()

  camada_setup_gmp()
  camada_ensure_deps_dirs()
  camada_select_mathsat_prebuilt_info(mathsat_url mathsat_archive
                                      mathsat_source_dir)

  camada_try_download_file("${mathsat_url}" "${mathsat_archive}"
                           mathsat_download_succeeded)
  if(NOT mathsat_download_succeeded)
    message(
      WARNING
        "Skipping MathSAT download because the vendor archive is currently unavailable."
    )
    return()
  endif()
  camada_extract_archive(
    ARCHIVE_PATH
    "${mathsat_archive}"
    DESTINATION_DIR
    "${CAMADA_DEPS_SRC_DIR}"
    MARKER_PATH
    "${mathsat_source_dir}/include/mathsat.h"
    ARCHIVE_URL
    "${mathsat_url}"
    SOURCE_DIR
    "${mathsat_source_dir}")

  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/lib")
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/include")

  if(CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    file(COPY "${mathsat_source_dir}/lib"
         DESTINATION "${CAMADA_DEPS_INSTALL_DIR}")
    file(COPY "${mathsat_source_dir}/include"
         DESTINATION "${CAMADA_DEPS_INSTALL_DIR}")
    if(EXISTS "/usr/local/include/gmp.h"
       AND NOT EXISTS "${CAMADA_DEPS_INSTALL_DIR}/include/gmp.h")
      execute_process(
        COMMAND ${CMAKE_COMMAND} -E create_symlink /usr/local/include/gmp.h
                "${CAMADA_DEPS_INSTALL_DIR}/include/gmp.h")
    endif()
    camada_stage_macos_mathsat_binary("${mathsat_source_dir}")
  else()
    file(COPY "${mathsat_source_dir}/lib/"
         DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/lib")
    file(COPY "${mathsat_source_dir}/include/"
         DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/include")
  endif()
endfunction()
