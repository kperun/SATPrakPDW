if(EXISTS "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/3.2.8.zip")
  file("MD5" "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/3.2.8.zip" hash_value)
  if("x${hash_value}" STREQUAL "xe368e3dd35e9a5f46a118029cabc494d")
    return()
  endif()
endif()
message(STATUS "downloading...
     src='https://bitbucket.org/eigen/eigen/get/3.2.8.zip'
     dst='/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/3.2.8.zip'
     timeout='none'")




file(DOWNLOAD
  "https://bitbucket.org/eigen/eigen/get/3.2.8.zip"
  "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/3.2.8.zip"
  SHOW_PROGRESS
  # no TIMEOUT
  STATUS status
  LOG log)

list(GET status 0 status_code)
list(GET status 1 status_string)

if(NOT status_code EQUAL 0)
  message(FATAL_ERROR "error: downloading 'https://bitbucket.org/eigen/eigen/get/3.2.8.zip' failed
  status_code: ${status_code}
  status_string: ${status_string}
  log: ${log}
")
endif()

message(STATUS "downloading... done")
