find_package(cvc5 PATHS ${CMAKE_SOURCE_DIR}/deps/install/)
set(CVC5_FOUND ${cvc5_FOUND})

if(CVC5_FOUND)
  # Remove any suffix from CVC5's version string
  string(REGEX REPLACE "([0-9]\\.[0-9]\\.[0-9]).*" "\\1" CVC5_VERSION
                       "${cvc5_VERSION}")

  set(CVC5_MIN_VERSION "1.0.8")
  if(CVC5_VERSION VERSION_LESS CVC5_MIN_VERSION)
    message(FATAL_ERROR "Expected version ${CVC5_MIN_VERSION} or greater")
  endif()
endif()
