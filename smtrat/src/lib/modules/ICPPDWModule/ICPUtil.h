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
            midpoint = interval.upper() - Settings::maxOriginalVarBound / 2.0;
          }
          else {
            // [lower, inf)
            midpoint = interval.lower() + Settings::maxOriginalVarBound / 2.0;
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

      /**
       * Checks whether the new interval bounds are strictly better than the old interval bounds.
       * e.g. [5,... is better than [6,...
       * e.g. ...,3) is better than ...,3]
       *
       * @param oldInterval the old interval
       * @param newInterval the new interval
       * @return a pair of booleans, representing: first is true iff the new lower bound is strictly better than the old lower bound
       *                                           second is true iff the new upper bound is strictly better than the old upper bound
       */
      static pair<bool,bool> isBoundBetter(IntervalT oldInterval, IntervalT newInterval) {
        bool isLowerBetter = false;
        bool isUpperBetter = false;

        if (newInterval.isEmpty()) {
          isLowerBetter = true;
          isUpperBetter = true;
        }
        else {
          if (oldInterval.lowerBoundType() == carl::BoundType::INFTY && newInterval.lowerBoundType() != carl::BoundType::INFTY) {
            isLowerBetter = true;
          }
          else if (oldInterval.lowerBoundType() != carl::BoundType::INFTY && newInterval.lowerBoundType() != carl::BoundType::INFTY) {
            if (newInterval.lower() > oldInterval.lower()) {
              isLowerBetter = true;
            }
            else if (oldInterval.lower() == newInterval.lower() && oldInterval.lowerBoundType() == carl::BoundType::WEAK && newInterval.lowerBoundType() == carl::BoundType::STRICT) {
              isLowerBetter = true;
            }
          }

          if (oldInterval.upperBoundType() == carl::BoundType::INFTY && newInterval.upperBoundType() != carl::BoundType::INFTY) {
            isUpperBetter = true;
          }
          else if (oldInterval.upperBoundType() != carl::BoundType::INFTY && newInterval.upperBoundType() != carl::BoundType::INFTY) {
            if (newInterval.upper() < oldInterval.upper()) {
              isUpperBetter = true;
            }
            else if (oldInterval.upper() == newInterval.upper() && oldInterval.upperBoundType() == carl::BoundType::WEAK && newInterval.upperBoundType() == carl::BoundType::STRICT) {
              isUpperBetter = true;
            }
          }
        }

        return pair<bool,bool>(isLowerBetter, isUpperBetter);
      }

      static OneOrTwo<ConstraintT> intervalToConstraint(carl::Variable var, const IntervalT& interval) {
        // since we cannot directly set the interval for a variable,
        // we will need to add two constraints. one for the lower and one for the upper bound
        // one advantage of this approach is that we can easily revert a contraction
        // by removing those constraints from the variable bounds

        ConstraintT upperBound;
        bool hasUpper = false;
        ConstraintT lowerBound;
        bool hasLower = false;

        // only consider strictly better lower bounds
        if (interval.lowerBoundType() != carl::BoundType::INFTY) {
          // x >= lower bound
          // lower bound - x <= 0
          Poly lowerPoly;
          lowerPoly -= var;
          lowerPoly += interval.lower();
          carl::Relation lowerRelation = (interval.lowerBoundType() == carl::BoundType::WEAK) ? carl::Relation::LEQ : carl::Relation::LESS;
          lowerBound = ConstraintT(lowerPoly, lowerRelation);
          hasLower = true;
        }

        // only consider strictly better upper bounds
        if (interval.upperBoundType() != carl::BoundType::INFTY) {
          // x <= upper bound
          // x - upper bound <= 0
          Poly upperPoly;
          upperPoly += var;
          upperPoly -= interval.upper();
          carl::Relation upperRelation = (interval.upperBoundType() == carl::BoundType::WEAK) ? carl::Relation::LEQ : carl::Relation::LESS;
          upperBound = ConstraintT(upperPoly, upperRelation);
          hasUpper = true;
        }

        if (hasUpper && hasLower) {
          return OneOrTwo<ConstraintT>(upperBound, lowerBound);
        }
        else if (hasUpper) {
          return OneOrTwo<ConstraintT>(upperBound, std::experimental::optional<ConstraintT>());
        }
        else /*if (hasLower)*/ {
          return OneOrTwo<ConstraintT>(lowerBound, std::experimental::optional<ConstraintT>());
        }
      }
  };
}
