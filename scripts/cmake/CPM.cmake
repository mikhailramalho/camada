set(CPM_DOWNLOAD_VERSION 0.38.1)

if(CPM_SOURCE_CACHE)
  set(CPM_DOWNLOAD_LOCATION
      "${CPM_SOURCE_CACHE}/cpm/CPM_${CPM_DOWNLOAD_VERSION}.cmake")
elseif(DEFINED ENV{CPM_SOURCE_CACHE})
  set(CPM_DOWNLOAD_LOCATION
      "$ENV{CPM_SOURCE_CACHE}/cpm/CPM_${CPM_DOWNLOAD_VERSION}.cmake")
else()
  set(CPM_DOWNLOAD_LOCATION
      "${CMAKE_BINARY_DIR}/cmake/CPM_${CPM_DOWNLOAD_VERSION}.cmake")
endif()

get_filename_component(CPM_DOWNLOAD_LOCATION ${CPM_DOWNLOAD_LOCATION} ABSOLUTE)

function(download_cpm)
  message(STATUS "Downloading CPM.cmake to ${CPM_DOWNLOAD_LOCATION}")
  file(
    DOWNLOAD
    https://github.com/cpm-cmake/CPM.cmake/releases/download/v${CPM_DOWNLOAD_VERSION}/CPM.cmake
    ${CPM_DOWNLOAD_LOCATION}
    STATUS download_status
    LOG download_log)
  list(GET download_status 0 download_status_code)
  list(GET download_status 1 download_status_message)

  if(download_status_code EQUAL 0)
    file(SIZE ${CPM_DOWNLOAD_LOCATION} download_size)
    if(download_size GREATER 0)
      return()
    endif()
    set(download_status_message
        "Downloaded CPM.cmake is empty after a successful transfer")
  endif()

  file(REMOVE ${CPM_DOWNLOAD_LOCATION})

  find_program(CURL_EXECUTABLE curl)
  if(CURL_EXECUTABLE)
    execute_process(
      COMMAND
        ${CURL_EXECUTABLE} -L --fail --output ${CPM_DOWNLOAD_LOCATION}
        https://github.com/cpm-cmake/CPM.cmake/releases/download/v${CPM_DOWNLOAD_VERSION}/CPM.cmake
      RESULT_VARIABLE curl_result
      OUTPUT_VARIABLE curl_stdout
      ERROR_VARIABLE curl_stderr)

    if(curl_result EQUAL 0 AND EXISTS ${CPM_DOWNLOAD_LOCATION})
      file(SIZE ${CPM_DOWNLOAD_LOCATION} download_size)
      if(download_size GREATER 0)
        return()
      endif()
      file(REMOVE ${CPM_DOWNLOAD_LOCATION})
      set(curl_stderr "${curl_stderr}\nDownloaded CPM.cmake is empty")
    endif()

    message(
      FATAL_ERROR
        "Failed to download CPM.cmake\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\ncurl exit code: ${curl_result}\nstdout:\n${curl_stdout}\nstderr:\n${curl_stderr}"
    )
  endif()

  message(
    FATAL_ERROR
      "Failed to download CPM.cmake\nfile(DOWNLOAD): ${download_status_code} ${download_status_message}\n${download_log}\nNo curl executable was found for a retry."
  )
endfunction()

if(NOT (EXISTS ${CPM_DOWNLOAD_LOCATION}))
  download_cpm()
else()
  file(READ ${CPM_DOWNLOAD_LOCATION} check)
  if("${check}" STREQUAL "")
    download_cpm()
  endif()
  unset(check)
endif()

include(${CPM_DOWNLOAD_LOCATION})
