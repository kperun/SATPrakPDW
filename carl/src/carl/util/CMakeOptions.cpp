#include <iostream>

#include "CMakeOptions.h"
#include <string>

namespace carl {

struct OptionPrinter {
	std::ostream& os;
	explicit OptionPrinter(std::ostream& out): os(out) {}
	void operator()(const std::string& name, const std::string& value) {
		if (name.at(0) == '_') return;
		if (value.find('\n') == std::string::npos) {
			os << name << " = " << value << std::endl;
		} else {
			os << name << " has multiple lines." << std::endl;
		}
	}
};

void printCMakeOptions(std::ostream& os) {
	OptionPrinter p(os);
	
	 p("ALLWARNINGS", R"VAR(OFF)VAR");
	 p("BIN_INSTALL_DIR", R"VAR(/usr/local/lib)VAR");
	 p("BUILD_STATIC", R"VAR(OFF)VAR");
	 p("CLANG_TIDY", R"VAR(CLANG_TIDY-NOTFOUND)VAR");
	 p("CMAKE_BUILD_TYPE", R"VAR()VAR");
	 p("CMAKE_INSTALL_DIR", R"VAR(/usr/local/lib/CMake/carl)VAR");
	 p("CMAKE_INSTALL_PREFIX", R"VAR(/usr/local)VAR");
	 p("COMPARE_WITH_Z3", R"VAR(OFF)VAR");
	 p("COVERAGE", R"VAR(OFF)VAR");
	 p("DEVELOPER", R"VAR(OFF)VAR");
	 p("EXECUTABLE_OUTPUT_PATH", R"VAR(/home/kperun/Dokumente/SATPraktikum/carl/build/bin)VAR");
	 p("EXPORT_TO_CMAKE", R"VAR(ON)VAR");
	 p("FORCE_SHIPPED_RESOURCES", R"VAR(OFF)VAR");
	 p("INCLUDE_INSTALL_DIR", R"VAR(/usr/local/include)VAR");
	 p("LIB_INSTALL_DIR", R"VAR(/usr/local/lib)VAR");
	 p("LOGGING", R"VAR(OFF)VAR");
	 p("LOGGING_CARL", R"VAR(OFF)VAR");
	 p("LOGGING_DISABLE_INEFFICIENT", R"VAR(OFF)VAR");
	 p("PRUNE_MONOMIAL_POOL", R"VAR(ON)VAR");
	 p("THREAD_SAFE", R"VAR(OFF)VAR");
	 p("USE_CLN_NUMBERS", R"VAR(OFF)VAR");
	 p("USE_COCOA", R"VAR(OFF)VAR");
	 p("USE_COTIRE", R"VAR(OFF)VAR");
	 p("USE_GINAC", R"VAR(OFF)VAR");
	 p("USE_MPFR_FLOAT", R"VAR(OFF)VAR");
	 p("USE_Z3_NUMBERS", R"VAR(OFF)VAR");
}

}
