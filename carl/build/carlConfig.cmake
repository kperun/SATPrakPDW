set(carl_VERSION 1.0.0)
   
get_filename_component(carl_CMAKE_DIR "${CMAKE_CURRENT_LIST_FILE}" PATH)


add_library(GMP_SHARED SHARED IMPORTED)
set_target_properties(GMP_SHARED PROPERTIES IMPORTED_LOCATION "/usr/lib/x86_64-linux-gnu/libgmp.so")
set_target_properties(GMP_SHARED PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "/usr/include/x86_64-linux-gnu")

add_library(GMP_STATIC STATIC IMPORTED)
set_target_properties(GMP_STATIC PROPERTIES IMPORTED_LOCATION "/usr/lib/x86_64-linux-gnu/libgmp.a")
set_target_properties(GMP_STATIC PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "/usr/include/x86_64-linux-gnu")

add_library(GMPXX_SHARED SHARED IMPORTED)
set_target_properties(GMPXX_SHARED PROPERTIES IMPORTED_LOCATION "/usr/lib/x86_64-linux-gnu/libgmpxx.so")
set_target_properties(GMPXX_SHARED PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "/usr/include")

add_library(GMPXX_STATIC STATIC IMPORTED)
set_target_properties(GMPXX_STATIC PROPERTIES IMPORTED_LOCATION "/usr/lib/x86_64-linux-gnu/libgmpxx.a")
set_target_properties(GMPXX_STATIC PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "/usr/include")
set_target_properties(GMPXX_STATIC PROPERTIES IMPORTED_LINK_INTERFACE_LIBRARIES "GMP_STATIC")

add_library(EIGEN3 INTERFACE IMPORTED)
set_target_properties(EIGEN3 PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/include")

add_library(GTESTCORE_STATIC STATIC IMPORTED)
set_target_properties(GTESTCORE_STATIC PROPERTIES IMPORTED_LOCATION "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-build/libgtest.a")
set_target_properties(GTESTCORE_STATIC PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP/include")

add_library(GTESTMAIN_STATIC STATIC IMPORTED)
set_target_properties(GTESTMAIN_STATIC PROPERTIES IMPORTED_LOCATION "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP-build/libgtest_main.a")
set_target_properties(GTESTMAIN_STATIC PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/GTest_EP/include")



set(CARL_LOGGING "OFF")
set(CARL_FORCE_SHIPPED_RESOURCES "OFF")
set(CARL_USE_GINAC "OFF")
set(CARL_USE_CLN_NUMBERS "OFF")
set(CARL_USE_COCOA "OFF")
set(CARL_USE_MPFR_FLOAT "OFF")
set(CARL_BUILD_STATIC "OFF")
set(CARL_THREAD_SAFE "OFF")
 
# Our library dependencies (contains definitions for IMPORTED targets)
if(NOT TARGET lib_carl AND NOT carl_BINARY_DIR)
  include("${carl_CMAKE_DIR}/carlTargets.cmake")
endif()


####### Expanded from @PACKAGE_INIT@ by configure_package_config_file() #######
####### Any changes to this file will be overwritten by the next CMake run ####
####### The input file was carlConfig.cmake.in                            ########

get_filename_component(PACKAGE_PREFIX_DIR "${CMAKE_CURRENT_LIST_DIR}/../../../" ABSOLUTE)

macro(set_and_check _var _file)
  set(${_var} "${_file}")
  if(NOT EXISTS "${_file}")
    message(FATAL_ERROR "File or directory ${_file} referenced by variable ${_var} does not exist !")
  endif()
endmacro()

macro(check_required_components _NAME)
  foreach(comp ${${_NAME}_FIND_COMPONENTS})
    if(NOT ${_NAME}_${comp}_FOUND)
      if(${_NAME}_FIND_REQUIRED_${comp})
        set(${_NAME}_FOUND FALSE)
      endif()
    endif()
  endforeach()
endmacro()

####################################################################################
   
set(carl_INCLUDE_DIR "/home/kperun/Dokumente/SATPraktikum/carl/src")

set(carl_LIBRARIES lib_carl)
check_required_components(carl)
