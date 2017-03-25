# Install script for directory: /home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/home/kperun/Dokumente/SATPraktikum/carl/build/resources")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Release")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

if(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Devel")
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/eigen3/unsupported/Eigen/src/IterativeSolvers" TYPE FILE FILES
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/GMRES.h"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/IncompleteCholesky.h"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/MINRES.h"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/Scaling.h"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/DGMRES.h"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/IncompleteLU.h"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/ConstrainedConjGrad.h"
    "/home/kperun/Dokumente/SATPraktikum/carl/build/resources/src/EIGEN3_REPO/unsupported/Eigen/src/IterativeSolvers/IterationController.h"
    )
endif()

