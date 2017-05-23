/*
 * File:   ICPUtil.h
 * Author: David
 */

#pragma once

#include "../../Common.h"

namespace smtrat
{
  /**
   * A collection of utility functions.
   */
  template<class Settings>
  class ICPUtil
  {
    public:

      /**
       * Determines whether a variable occurs in a set of constraints.
       * @param var the variable
       * @param constraints the set of constraints
       * @return true if the variable is contained in the set of constraints
       */
      static bool occursVariableInConstraints(carl::Variable var, std::set<ConstraintT> constraints) {
        for (const ConstraintT& c : constraints) {
          if (c.lhs().has(var)) {
            return true;
          }
        }
        return false;
      }

      /**
       * Splits the given interval into two non-empty pieces.
       * @param interval the interval that should be splitted
       * @return a pair of two new non-empty intervals which 
       */
      static std::pair<IntervalT, IntervalT> splitInterval(IntervalT interval) {
        double midpoint = 0.0;
        if (interval.isHalfBounded()) {
          if (interval.lowerBoundType() == carl::BoundType::INFTY) {
            // (-inf, upper]
            midpoint = interval.upper() - Settings::maxOriginalVarBound;
          }
          else {
            // [lower, inf)
            midpoint = interval.lower() + Settings::maxOriginalVarBound;
          }
        }
        else if (interval.isInfinite()) {
          // (-inf, inf)
          midpoint = 0.0;
        }
        else {
          midpoint = interval.lower() + interval.diameter() / 2.0;
        }


        IntervalT firstNewInterval(interval.lower(), interval.lowerBoundType(), midpoint, carl::BoundType::WEAK);
        IntervalT secondNewInterval(midpoint, carl::BoundType::STRICT, interval.upper(), interval.upperBoundType());
        return std::make_pair(firstNewInterval, secondNewInterval);
      }
  };
}
