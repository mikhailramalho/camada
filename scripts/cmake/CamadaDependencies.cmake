set(
  CAMADA_DOWNLOAD_DEPENDENCIES
  "OFF"
  CACHE STRING
        "Download missing solver dependencies during CMake configure: OFF, ALL, or PERMISSIVE-ONLY")
set_property(CACHE CAMADA_DOWNLOAD_DEPENDENCIES PROPERTY STRINGS OFF ALL
                                                             PERMISSIVE-ONLY)

if(NOT CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "OFF"
   AND NOT CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "ALL"
   AND NOT CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "PERMISSIVE-ONLY")
  message(
    FATAL_ERROR
      "CAMADA_DOWNLOAD_DEPENDENCIES must be one of: OFF, ALL, PERMISSIVE-ONLY"
  )
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
    "https://github.com/Z3Prover/z3/releases/download/z3-4.16.0/z3-4.16.0-x64-glibc-2.39.zip"
    CACHE STRING "URL used to download the prebuilt Z3 archive for Linux x86_64")
set(CAMADA_Z3_LINUX_AARCH64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.16.0/z3-4.16.0-arm64-glibc-2.38.zip"
    CACHE STRING "URL used to download the prebuilt Z3 archive for Linux aarch64")
set(CAMADA_Z3_MACOS_X86_64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.16.0/z3-4.16.0-x64-osx-15.7.3.zip"
    CACHE STRING "URL used to download the prebuilt Z3 archive for macOS x86_64")
set(CAMADA_Z3_MACOS_ARM64_URL
    "https://github.com/Z3Prover/z3/releases/download/z3-4.16.0/z3-4.16.0-arm64-osx-15.7.3.zip"
    CACHE STRING "URL used to download the prebuilt Z3 archive for macOS arm64")
set(CAMADA_CVC5_LINUX_X86_64_URL
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.3/cvc5-Linux-x86_64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt cvc5 archive for Linux x86_64")
set(CAMADA_CVC5_LINUX_AARCH64_URL
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.3/cvc5-Linux-arm64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt cvc5 archive for Linux aarch64")
set(CAMADA_CVC5_MACOS_X86_64_URL
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.3/cvc5-macOS-x86_64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt cvc5 archive for macOS x86_64")
set(CAMADA_BITWUZLA_LINUX_X86_64_URL
    "https://github.com/bitwuzla/bitwuzla/releases/download/0.9.0/Bitwuzla-Linux-x86_64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt Bitwuzla archive for Linux x86_64")
set(CAMADA_BITWUZLA_LINUX_AARCH64_URL
    "https://github.com/bitwuzla/bitwuzla/releases/download/0.9.0/Bitwuzla-Linux-arm64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt Bitwuzla archive for Linux aarch64")
set(CAMADA_BITWUZLA_MACOS_ARM64_URL
    "https://github.com/bitwuzla/bitwuzla/releases/download/0.9.0/Bitwuzla-macOS-arm64-static.zip"
    CACHE STRING
          "URL used to download the prebuilt Bitwuzla archive for macOS arm64")
set(CAMADA_MATHSAT_VERSION
    "5.6.15"
    CACHE STRING "MathSAT release version used for prebuilt downloads")
set(CAMADA_MATHSAT_LINUX_X86_64_URL
    "https://mathsat.fbk.eu/release/mathsat-5.6.15-linux-x86_64.tar.gz"
    CACHE STRING "URL used to download MathSAT for Linux x86_64")
set(CAMADA_MATHSAT_LINUX_AARCH64_URL
    "https://mathsat.fbk.eu/release/mathsat-5.6.15-linux-aarch64.tar.gz"
    CACHE STRING "URL used to download MathSAT for Linux aarch64")
set(CAMADA_MATHSAT_MACOS_X86_64_URL
    "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.15-osx.tar.gz"
    CACHE STRING "URL used to download MathSAT for macOS x86_64")
set(CAMADA_MATHSAT_MACOS_ARM64_URL
    "https://mathsat.fbk.eu/release/mathsat-5.6.15-macos.tar.gz"
    CACHE STRING "URL used to download MathSAT for macOS arm64")

function(camada_ensure_deps_dirs)
  file(MAKE_DIRECTORY "${CAMADA_DEPS_DIR}")
  file(MAKE_DIRECTORY "${CAMADA_DEPS_SRC_DIR}")
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}")
endfunction()

function(camada_should_download_dependency out_var is_permissive)
  if(CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "ALL")
    set(${out_var} TRUE PARENT_SCOPE)
    return()
  endif()

  if(CAMADA_DOWNLOAD_DEPENDENCIES STREQUAL "PERMISSIVE-ONLY"
     AND is_permissive)
    set(${out_var} TRUE PARENT_SCOPE)
    return()
  endif()

  set(${out_var} FALSE PARENT_SCOPE)
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
  file(DOWNLOAD "${url}" "${output_path}" STATUS download_status
       LOG download_log SHOW_PROGRESS)
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
      set(${result_var} TRUE PARENT_SCOPE)
      return()
    endif()
    file(REMOVE "${output_path}")
  endif()

  message(STATUS "Downloading ${url}")
  file(DOWNLOAD "${url}" "${output_path}" STATUS download_status
       LOG download_log SHOW_PROGRESS)
  list(GET download_status 0 download_status_code)
  list(GET download_status 1 download_status_message)

  if(download_status_code EQUAL 0)
    file(SIZE "${output_path}" output_size)
    if(output_size GREATER 0)
      set(${result_var} TRUE PARENT_SCOPE)
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
        set(${result_var} TRUE PARENT_SCOPE)
        return()
      endif()
      file(REMOVE "${output_path}")
      set(curl_stderr "${curl_stderr}\nDownloaded file is empty")
    endif()

    message(
      WARNING
        "Failed to download ${url}\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\ncurl exit code: ${curl_result}\nstdout:\n${curl_stdout}\nstderr:\n${curl_stderr}"
    )
    set(${result_var} FALSE PARENT_SCOPE)
    return()
  endif()

  message(
    WARNING
      "Failed to download ${url}\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\nNo curl executable was found for a retry."
  )
  set(${result_var} FALSE PARENT_SCOPE)
endfunction()

function(camada_extract_archive)
  set(options)
  set(one_value_args ARCHIVE_PATH DESTINATION_DIR MARKER_PATH ARCHIVE_URL SOURCE_DIR)
  cmake_parse_arguments(CAMADA_EXTRACT "${options}" "${one_value_args}" "" ${ARGN})

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

    if(_camada_extract_result EQUAL 0 AND EXISTS "${CAMADA_EXTRACT_MARKER_PATH}")
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
        set(${output_var} "${CAMADA_${package_name}_LINUX_X86_64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    elseif(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)$")
      if(DEFINED CAMADA_${package_name}_LINUX_AARCH64_URL
         AND NOT CAMADA_${package_name}_LINUX_AARCH64_URL STREQUAL "")
        set(${output_var} "${CAMADA_${package_name}_LINUX_AARCH64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    endif()
  elseif(CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64)$")
      if(DEFINED CAMADA_${package_name}_MACOS_X86_64_URL
         AND NOT CAMADA_${package_name}_MACOS_X86_64_URL STREQUAL "")
        set(${output_var} "${CAMADA_${package_name}_MACOS_X86_64_URL}"
            PARENT_SCOPE)
        return()
      endif()
    elseif(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)$")
      if(DEFINED CAMADA_${package_name}_MACOS_ARM64_URL
         AND NOT CAMADA_${package_name}_MACOS_ARM64_URL STREQUAL "")
        set(${output_var} "${CAMADA_${package_name}_MACOS_ARM64_URL}"
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
      set(${output_url_var} "${CAMADA_MATHSAT_MACOS_X86_64_URL}" PARENT_SCOPE)
      set(${output_archive_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-osx.tar.gz"
          PARENT_SCOPE)
      set(${output_source_dir_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-osx"
          PARENT_SCOPE)
      return()
    endif()
    if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)$")
      set(${output_url_var} "${CAMADA_MATHSAT_MACOS_ARM64_URL}" PARENT_SCOPE)
      set(${output_archive_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-macos.tar.gz"
          PARENT_SCOPE)
      set(${output_source_dir_var}
          "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-macos"
          PARENT_SCOPE)
      return()
    endif()
    message(
      FATAL_ERROR
        "No prebuilt MathSAT archive configured for host system '${CMAKE_HOST_SYSTEM_NAME}' and processor '${CMAKE_HOST_SYSTEM_PROCESSOR}'"
    )
  endif()

  if(CMAKE_HOST_SYSTEM_NAME MATCHES "Linux"
     AND CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(x86_64|amd64)$")
    set(${output_url_var} "${CAMADA_MATHSAT_LINUX_X86_64_URL}" PARENT_SCOPE)
    set(
      ${output_archive_var}
      "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-linux-x86_64.tar.gz"
      PARENT_SCOPE)
    set(
      ${output_source_dir_var}
      "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-linux-x86_64"
      PARENT_SCOPE)
    return()
  endif()

  if(CMAKE_HOST_SYSTEM_NAME MATCHES "Linux"
     AND CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "^(aarch64|arm64)$")
    set(${output_url_var} "${CAMADA_MATHSAT_LINUX_AARCH64_URL}" PARENT_SCOPE)
    set(
      ${output_archive_var}
      "${CAMADA_DEPS_SRC_DIR}/mathsat-${CAMADA_MATHSAT_VERSION}-linux-aarch64.tar.gz"
      PARENT_SCOPE)
    set(
      ${output_source_dir_var}
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
  CPMAddPackage(
    NAME ${package_name}
    DOWNLOAD_ONLY YES
    GITHUB_REPOSITORY ${repository}
    GIT_TAG ${git_tag}
    GIT_PROGRESS TRUE)
  set(${out_var} "${${package_name}_SOURCE_DIR}" PARENT_SCOPE)
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
    OUTPUT_QUIET
    ERROR_QUIET)
  if(NOT symlink_result EQUAL 0)
    file(COPY "${fetched_source_dir}" DESTINATION "${dependency_dir}/..")
    get_filename_component(dependency_name "${dependency_dir}" NAME)
    set(copied_dependency_dir "${dependency_dir}/../${dependency_name}")
    if(NOT copied_dependency_dir STREQUAL dependency_dir)
      file(RENAME "${copied_dependency_dir}" "${dependency_dir}")
    endif()
  endif()
endfunction()

function(camada_setup_cryptominisat_solver_deps cms_source_dir)
  get_filename_component(cms_parent_dir "${cms_source_dir}" DIRECTORY)
  set(cms_cadical_dir "${cms_parent_dir}/cadical")

  if(NOT EXISTS "${cms_cadical_dir}/build/libcadical.a"
     OR NOT EXISTS "${cms_cadical_dir}/src/cadical.hpp")
    camada_fetch_git_source(cryptominisat_cadical arminbiere/cadical rel-1.4.0
                            cms_cadical_source_dir)
    camada_prepare_cryptominisat_dependency_layout("${cms_cadical_dir}"
                                                   "${cms_cadical_source_dir}")
    camada_run_checked(
      WORKING_DIRECTORY "${cms_cadical_dir}"
      MESSAGE "Configuring CryptoMiniSat CaDiCaL"
      COMMAND ./configure -fPIC -O3)
    camada_run_checked(
      WORKING_DIRECTORY "${cms_cadical_dir}/build"
      MESSAGE "Building CryptoMiniSat CaDiCaL"
      COMMAND make -j libcadical.a)
  endif()
endfunction()

function(camada_setup_cryptominisat)
  set(cms_config
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cryptominisat5/cryptominisat5Config.cmake")
  if(EXISTS "${cms_config}")
    return()
  endif()

  camada_ensure_deps_dirs()
  camada_fetch_git_source(cryptominisat msoos/cryptominisat 5.6.3 cms_source_dir)
  camada_setup_cryptominisat_solver_deps("${cms_source_dir}")

  set(cms_build_dir "${cms_source_dir}/build")
  file(REMOVE_RECURSE "${cms_build_dir}")
  file(MAKE_DIRECTORY "${cms_build_dir}")

  camada_run_checked(
    WORKING_DIRECTORY "${cms_build_dir}"
    MESSAGE "Configuring CryptoMiniSat"
    COMMAND
      ${CMAKE_COMMAND} .. -GNinja -DSTATICCOMPILE=ON -DONLY_SIMPLE=ON
      -DENABLE_PYTHON_INTERFACE=OFF -DNOM4RI=ON -DCMAKE_BUILD_TYPE=Release
      -DCMAKE_INSTALL_PREFIX=${CAMADA_DEPS_INSTALL_DIR})
  camada_run_checked(
    WORKING_DIRECTORY "${cms_build_dir}"
    MESSAGE "Building CryptoMiniSat"
    COMMAND ninja)
  camada_run_checked(
    WORKING_DIRECTORY "${cms_build_dir}"
    MESSAGE "Installing CryptoMiniSat"
    COMMAND ninja install)
endfunction()

function(camada_setup_gmp)
  set(gmp_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libgmp.a")
  if(EXISTS "${gmp_lib}")
    return()
  endif()

  camada_ensure_deps_dirs()
  camada_fetch_git_source(gmp gmp-mirror/gmp 141ed4f98a50 gmp_source_dir)

  camada_run_checked(
    WORKING_DIRECTORY "${gmp_source_dir}"
    MESSAGE "Preparing GMP"
    COMMAND autoreconf -fi)
  camada_run_checked(
    WORKING_DIRECTORY "${gmp_source_dir}"
    MESSAGE "Configuring GMP"
    COMMAND ./configure --prefix=${CAMADA_DEPS_INSTALL_DIR} --disable-shared
            ABI=64 CFLAGS=-fPIC CPPFLAGS=-DPIC)
  camada_run_checked(
    WORKING_DIRECTORY "${gmp_source_dir}/doc"
    MESSAGE "Preparing GMP docs"
    COMMAND make stamp-vti)
  camada_run_checked(
    WORKING_DIRECTORY "${gmp_source_dir}"
    MESSAGE "Building GMP"
    COMMAND make -j)
  camada_run_checked(
    WORKING_DIRECTORY "${gmp_source_dir}"
    MESSAGE "Installing GMP"
    COMMAND make install)
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

  camada_run_checked(
    WORKING_DIRECTORY "${minisat_source_dir}"
    MESSAGE "Configuring Minisat"
    COMMAND make config BUILD_DIR=build prefix=${minisat_prefix})
  camada_run_checked(
    WORKING_DIRECTORY "${minisat_source_dir}"
    MESSAGE "Building Minisat"
    COMMAND make -j CXXFLAGS=-fPIC build/release/lib/libminisat.a)

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

function(camada_setup_bitwuzla)
  if(NOT EXISTS "${CAMADA_DEPS_INSTALL_DIR}/include/bitwuzla/c/bitwuzla.h")
    camada_ensure_deps_dirs()
    camada_select_prebuilt_url(bitwuzla_url BITWUZLA)

    get_filename_component(bitwuzla_archive_name "${bitwuzla_url}" NAME)
    string(REGEX REPLACE "\\.zip$" "" bitwuzla_root_dir_name
                         "${bitwuzla_archive_name}")
    set(bitwuzla_archive "${CAMADA_DEPS_SRC_DIR}/${bitwuzla_archive_name}")
    set(bitwuzla_root_dir "${CAMADA_DEPS_SRC_DIR}/${bitwuzla_root_dir_name}")

    camada_download_file("${bitwuzla_url}" "${bitwuzla_archive}")
    camada_extract_archive(
      ARCHIVE_PATH "${bitwuzla_archive}"
      DESTINATION_DIR "${CAMADA_DEPS_SRC_DIR}"
      MARKER_PATH "${bitwuzla_root_dir}"
      ARCHIVE_URL "${bitwuzla_url}"
      SOURCE_DIR "${bitwuzla_root_dir}")
    camada_stage_prebuilt_tree("${bitwuzla_root_dir}")
  endif()

  file(
    GLOB bitwuzla_pc_files
    "${CAMADA_DEPS_INSTALL_DIR}/lib/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib/*/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/pkgconfig/bitwuzla.pc"
    "${CAMADA_DEPS_INSTALL_DIR}/lib64/*/pkgconfig/bitwuzla.pc")
  foreach(bitwuzla_pc_file IN LISTS bitwuzla_pc_files)
    get_filename_component(bitwuzla_pkgconfig_dir "${bitwuzla_pc_file}" DIRECTORY)
    get_filename_component(bitwuzla_libdir "${bitwuzla_pkgconfig_dir}" DIRECTORY)
    file(
      WRITE "${bitwuzla_pc_file}"
      "prefix=${CAMADA_DEPS_INSTALL_DIR}\nincludedir=\${prefix}/include\nlibdir=${bitwuzla_libdir}\n\nName: bitwuzla\nDescription: bitwuzla: bitwuzla\nVersion: 0.9.0\nRequires: gmp >= 6.3, mpfr >= 4.2.1\nLibs: -L\${libdir} -lbitwuzla -lbitwuzlals -lbitwuzlabv -lbitwuzlabb\nCflags: -I\${includedir}\n"
    )
  endforeach()
endfunction()

function(camada_setup_cvc5)
  set(cvc5_config "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cvc5/cvc5Config.cmake")
  if(EXISTS "${cvc5_config}")
    file(READ "${cvc5_config}" cvc5_config_contents)
    string(REPLACE "set(CVC5_BINDINGS_JAVA ON)" "set(CVC5_BINDINGS_JAVA OFF)"
                   cvc5_config_contents "${cvc5_config_contents}")
    file(WRITE "${cvc5_config}" "${cvc5_config_contents}")
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
    ARCHIVE_PATH "${cvc5_archive}"
    DESTINATION_DIR "${CAMADA_DEPS_SRC_DIR}"
    MARKER_PATH "${cvc5_root_dir}"
    ARCHIVE_URL "${cvc5_url}"
    SOURCE_DIR "${cvc5_root_dir}")
  camada_stage_prebuilt_tree("${cvc5_root_dir}")
  file(READ "${cvc5_config}" cvc5_config_contents)
  string(REPLACE "set(CVC5_BINDINGS_JAVA ON)" "set(CVC5_BINDINGS_JAVA OFF)"
                 cvc5_config_contents "${cvc5_config_contents}")
  file(WRITE "${cvc5_config}" "${cvc5_config_contents}")
endfunction()

function(camada_setup_stp)
  set(stp_config "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/STP/STPConfig.cmake")
  if(EXISTS "${stp_config}")
    return()
  endif()

  message(
    STATUS
      "The STP 2.3.4_cadical GitHub release asset is a standalone solver binary, not a development package with headers and libraries. Falling back to a source build for Camada's STP API wrapper."
  )

  camada_setup_minisat()
  camada_setup_cryptominisat()
  camada_fetch_git_source(stpsrc stp/stp 2.3.4 stp_source_dir)

  set(stp_build_dir "${stp_source_dir}/build")
  set(cms_config_dir
      "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/cryptominisat5")
  file(REMOVE_RECURSE "${stp_build_dir}")
  file(MAKE_DIRECTORY "${stp_build_dir}")

  camada_run_checked(
    WORKING_DIRECTORY "${stp_build_dir}"
    MESSAGE "Configuring STP"
    COMMAND ${CMAKE_COMMAND} .. -GNinja -DONLY_SIMPLE=ON
            -DCMAKE_INSTALL_PREFIX=${CAMADA_DEPS_INSTALL_DIR}
            -DCMAKE_BUILD_TYPE=Release -DBUILD_EXECUTABLES=OFF
            -DSTATICCOMPILE=ON -DBUILD_SHARED_LIBS=OFF
            -Dminisat_DIR=${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/minisat
            -Dcryptominisat5_DIR=${cms_config_dir})
  camada_run_checked(
    WORKING_DIRECTORY "${stp_build_dir}"
    MESSAGE "Building STP"
    COMMAND ninja)
  camada_run_checked(
    WORKING_DIRECTORY "${stp_build_dir}"
    MESSAGE "Installing STP"
    COMMAND ninja install)
endfunction()

function(camada_setup_yices)
  set(yices_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libyices.a")
  set(yices_header "${CAMADA_DEPS_INSTALL_DIR}/include/yices.h")
  set(yices_shared_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libyices.so")
  set(yices_shared_soname "${CAMADA_DEPS_INSTALL_DIR}/lib/libyices.so.2.7.0")
  set(yices_source_stamp "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/yices/camada-source-build.stamp")
  if(BUILD_SHARED_LIBS AND EXISTS "${yices_shared_lib}" AND EXISTS "${yices_header}"
     AND EXISTS "${yices_source_stamp}")
    return()
  endif()
  if(NOT BUILD_SHARED_LIBS AND EXISTS "${yices_lib}" AND EXISTS "${yices_header}")
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
  camada_run_checked(
    WORKING_DIRECTORY "${yices_source_dir}"
    MESSAGE "Preparing Yices"
    COMMAND autoreconf)
  camada_run_checked(
    WORKING_DIRECTORY "${yices_source_dir}"
    MESSAGE "Configuring Yices"
    COMMAND ./configure --prefix ${CAMADA_DEPS_INSTALL_DIR}
            --with-static-gmp=${CAMADA_DEPS_INSTALL_DIR}/lib/libgmp.a
            LDFLAGS=-L${CAMADA_DEPS_INSTALL_DIR}/lib/)
  camada_run_checked(
    WORKING_DIRECTORY "${yices_source_dir}"
    MESSAGE "Building Yices"
    COMMAND make -j)
  camada_run_checked(
    WORKING_DIRECTORY "${yices_source_dir}"
    MESSAGE "Building Yices static library"
    COMMAND make static-lib)
  camada_run_checked(
    WORKING_DIRECTORY "${yices_source_dir}"
    MESSAGE "Installing Yices"
    COMMAND make install)
  file(MAKE_DIRECTORY "${CAMADA_DEPS_INSTALL_DIR}/lib/cmake/yices")
  file(WRITE "${yices_source_stamp}" "1\n")
endfunction()

function(camada_setup_z3)
  set(z3_lib "${CAMADA_DEPS_INSTALL_DIR}/lib/libz3.a")
  if(BUILD_SHARED_LIBS)
    set(z3_lib "${CAMADA_DEPS_INSTALL_DIR}/bin/libz3${CMAKE_SHARED_LIBRARY_SUFFIX}")
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
    ARCHIVE_PATH "${z3_archive}"
    DESTINATION_DIR "${CAMADA_DEPS_SRC_DIR}"
    MARKER_PATH "${z3_root_dir}"
    ARCHIVE_URL "${z3_url}"
    SOURCE_DIR "${z3_root_dir}")
  camada_stage_prebuilt_tree("${z3_root_dir}")
endfunction()

function(camada_setup_mathsat)
  set(mathsat_header "${CAMADA_DEPS_INSTALL_DIR}/include/mathsat.h")
  if(EXISTS "${mathsat_header}")
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
    ARCHIVE_PATH "${mathsat_archive}"
    DESTINATION_DIR "${CAMADA_DEPS_SRC_DIR}"
    MARKER_PATH "${mathsat_source_dir}/include/mathsat.h"
    ARCHIVE_URL "${mathsat_url}"
    SOURCE_DIR "${mathsat_source_dir}")

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
  else()
    file(COPY "${mathsat_source_dir}/lib/"
         DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/lib")
    file(COPY "${mathsat_source_dir}/include/"
         DESTINATION "${CAMADA_DEPS_INSTALL_DIR}/include")
  endif()
endfunction()
