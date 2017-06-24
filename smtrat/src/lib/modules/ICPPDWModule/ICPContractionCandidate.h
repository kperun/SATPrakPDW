/*
 * File:   ContractionCandidate.h
 * Author: David
 */

#pragma once

#include "ICPPDWSettings.h"
#include "../../Common.h"
#include "../../datastructures/VariableBounds.h"
#include "carl/interval/Contraction.h"

namespace smtrat
{
  /**
   * This class represents a contraction candidate (x, c)
   * where x is a variable and c is a constraint.
   */
  template<class Settings>
  class ICPContractionCandidate
  {
    private:
      carl::Variable mVariable;
      ConstraintT mConstraint;

      // the solution formula of this contraction candidate
      carl::VarSolutionFormula<Poly> mSolutionFormula;

      // the actual relation used for propagation,
      // i.e. flipped constraint if the coefficient of var is negative
      carl::Relation mRelation;

      //the current weight as used in the reinforced learning
      // we initialize it with the value -1 in order to distinguish initialized and not initialized weights
      double mWeight = -1;

    public:
      ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint);

      /**
       * Calculates the contracted interval of this contraction candidate.
       * I.e., it will solve the constraint for mVariable and insert the given variable bounds.
       * The result may be either one or two intervals, depending on the order of the variable.
       *
       * @param intervalMap The variable bounds
       * @return one or two resulting intervals
       */
      OneOrTwo<IntervalT> getContractedInterval(const EvalDoubleIntervalMap& intervalMap);

      /**
       * Compute the new interval, subsequently the gain by the formula 1- D_new/D_old
       * @param intervalMap The variable bounds
       */
      double computeGain(const EvalDoubleIntervalMap& intervalMap);

      carl::Variable getVariable();
      ConstraintT& getConstraint();
      double getWeight();
      void setWeight(double weight);


      friend inline std::ostream& operator <<(std::ostream& os, const ICPContractionCandidate& cc) {
        os << "(" << cc.mVariable << ", " << cc.mConstraint << ")";
        return os;
      }
  };
}
