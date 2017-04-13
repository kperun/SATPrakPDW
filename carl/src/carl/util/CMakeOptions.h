/**
 * @file CMakeOptions.h.in
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <iostream>

namespace carl {

void printCMakeOptions(std::ostream& os);

namespace cmakeoptions {

	static constexpr auto _ALLWARNINGS = "OFF";
	static constexpr auto _BIN_INSTALL_DIR = "/usr/local/lib";
	static constexpr auto _BUILD_STATIC = "OFF";
	static constexpr auto _CARL_TARGETS = "lib_carl";
	static constexpr auto _CLANG_TIDY = "CLANG_TIDY-NOTFOUND";
	static constexpr auto _CMAKE_BUILD_TYPE = "";
	static constexpr auto _CMAKE_INSTALL_DIR = "/usr/local/lib/CMake/carl";
	static constexpr auto _CMAKE_INSTALL_PREFIX = "/usr/local";
	static constexpr auto _COMPARE_WITH_Z3 = "OFF";
	static constexpr auto _COVERAGE = "OFF";
	static constexpr auto _DEVELOPER = "OFF";
	static constexpr auto _EXECUTABLE_OUTPUT_PATH = "/home/kperun/Dropbox/So2017/SATPrak/SATPrakPDW/carl/build/bin";
	static constexpr auto _EXPORT_TO_CMAKE = "ON";
	static constexpr auto _FORCE_SHIPPED_RESOURCES = "OFF";
	static constexpr auto _INCLUDE_INSTALL_DIR = "/usr/local/include";
	static constexpr auto _LIB_INSTALL_DIR = "/usr/local/lib";
	static constexpr auto _LOGGING = "OFF";
	static constexpr auto _LOGGING_CARL = "OFF";
	static constexpr auto _LOGGING_DISABLE_INEFFICIENT = "OFF";
	static constexpr auto _PRUNE_MONOMIAL_POOL = "ON";
	static constexpr auto _THREAD_SAFE = "OFF";
	static constexpr auto _USE_CLN_NUMBERS = "OFF";
	static constexpr auto _USE_COCOA = "OFF";
	static constexpr auto _USE_COTIRE = "OFF";
	static constexpr auto _USE_GINAC = "OFF";
	static constexpr auto _USE_MPFR_FLOAT = "OFF";
	static constexpr auto _USE_Z3_NUMBERS = "OFF";
}

}
