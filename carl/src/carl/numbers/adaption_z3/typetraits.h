/** 
 * @file   adaption_gmpxx/typetraits.h
 * @ingroup typetraits
 * @ingroup gmpxx
 * @author Sebastian Junges
 * @author Gereon Kremer
 *
 */
#pragma once

#include "../../util/platform.h"
CLANG_WARNING_DISABLE("-Wsign-conversion")
#include <gmpxx.h>
CLANG_WARNING_RESET

#include "../typetraits.h"

namespace carl {
	
TRAIT_TRUE(is_integer, mpz, z3);
TRAIT_TRUE(is_rational, mpq, z3);
TRAIT_TRUE(is_rational, rational, z3);

TRAIT_TYPE(IntegralType, mpq, mpz, z3);
TRAIT_TYPE(IntegralType, mpz, mpz, z3);
}
