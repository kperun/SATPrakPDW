if("release-1.7.0" STREQUAL "")
  message(FATAL_ERROR "Tag for git checkout should not be empty.")
endif()

set(run 0)

if("/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-stamp/GTest_EP-gitinfo.txt" IS_NEWER_THAN "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-stamp/GTest_EP-gitclone-lastrun.txt")
  set(run 1)
endif()

if(NOT run)
  message(STATUS "Avoiding repeated git clone, stamp file is up to date: '/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-stamp/GTest_EP-gitclone-lastrun.txt'")
  return()
endif()

execute_process(
  COMMAND ${CMAKE_COMMAND} -E remove_directory "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to remove directory: '/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP'")
endif()

# try the clone 3 times incase there is an odd git clone issue
set(error_code 1)
set(number_of_tries 0)
while(error_code AND number_of_tries LESS 3)
  execute_process(
    COMMAND "/usr/bin/git" clone --origin "origin" "https://github.com/google/googletest.git" "GTest_EP"
    WORKING_DIRECTORY "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src"
    RESULT_VARIABLE error_code
    )
  math(EXPR number_of_tries "${number_of_tries} + 1")
endwhile()
if(number_of_tries GREATER 1)
  message(STATUS "Had to git clone more than once:
          ${number_of_tries} times.")
endif()
if(error_code)
  message(FATAL_ERROR "Failed to clone repository: 'https://github.com/google/googletest.git'")
endif()

execute_process(
  COMMAND "/usr/bin/git" checkout release-1.7.0
  WORKING_DIRECTORY "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to checkout tag: 'release-1.7.0'")
endif()

execute_process(
  COMMAND "/usr/bin/git" submodule init 
  WORKING_DIRECTORY "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to init submodules in: '/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP'")
endif()

execute_process(
  COMMAND "/usr/bin/git" submodule update --recursive 
  WORKING_DIRECTORY "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to update submodules in: '/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP'")
endif()

# Complete success, update the script-last-run stamp file:
#
execute_process(
  COMMAND ${CMAKE_COMMAND} -E copy
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-stamp/GTest_EP-gitinfo.txt"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-stamp/GTest_EP-gitclone-lastrun.txt"
  WORKING_DIRECTORY "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP"
  RESULT_VARIABLE error_code
  )
if(error_code)
  message(FATAL_ERROR "Failed to copy script-last-run stamp file: '/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-stamp/GTest_EP-gitclone-lastrun.txt'")
endif()

