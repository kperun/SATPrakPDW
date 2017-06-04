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
       * Determines whether any variable of a given set of variable occurs in a given constraint.
       * @param vars the set of variables
       * @param constraints the constraint
       * @return true if one of the variables is contained in the constraint
       */
      static bool occurVariablesInConstraint(std::set<carl::Variable> vars, ConstraintT constraint) {
        for (const carl::Variable& v : vars) {
          if (constraint.lhs().has(v)) {
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
            midpoint = (interval.upper() - Settings::maxOriginalVarBound) / 2;
          }
          else {
            // [lower, inf)
            midpoint = (interval.lower() + Settings::maxOriginalVarBound) / 2;
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

      /**
       * Checks whether the constraints represents a simple bound that can be directly used in VariableBound.
       * A simple bound is a constraint of the form a*x - b ~ 0.
       * @param constraint the constraint to check
       * @return true if it is a simple bound
       */
      static bool isSimpleBound(ConstraintT constraint) {
        const carl::Variable& var = *constraint.variables().begin();
        return (constraint.variables().size() == 1 && constraint.maxDegree(var) == 1);
      }
  };
}
