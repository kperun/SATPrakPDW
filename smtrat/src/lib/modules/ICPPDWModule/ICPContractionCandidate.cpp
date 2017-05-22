#include "ICPContractionCandidate.h"

namespace smtrat
{
  /**
   * We need a custom copy-constructor because Contractor is non-copyable...
   */
  ICPContractionCandidate::ICPContractionCandidate(const ICPContractionCandidate& rhs):
    mVariable(rhs.mVariable),
    mConstraint(rhs.mConstraint),
    mContractor(Contractor<carl::SimpleNewton>(rhs.mConstraint.lhs(), rhs.mConstraint.lhs()))
  {
  }

  ICPContractionCandidate::ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint):
    mVariable(var),
    mConstraint(constraint),
    mContractor(constraint.lhs(), constraint.lhs())
  {
  }

  ICPContractionCandidate::~ICPContractionCandidate() {
  }

  carl::Variable ICPContractionCandidate::getVariable() {
    return mVariable;
  }

  ConstraintT& ICPContractionCandidate::getConstraint() {
    return mConstraint;
  }


  OneOrTwo<IntervalT> ICPContractionCandidate::getContractedInterval(const vb::VariableBounds<ConstraintT>& _bounds) {
    // first retrieve all variables with their respective bounds
    auto& map = _bounds.getIntervalMap();

    // possible are two intervals resulting from a split
    IntervalT resultA, resultB;
    std::experimental::optional<IntervalT> retB;

    // apply contraction
    // arguments are true because we want to use propagation
    bool split = mContractor(map, mVariable, resultA, resultB, true, true);

    /*
     * The contractor only solves for equality, i.e. it solves polynomial = 0 for the variable.
     * In case our constraint was an inequality, we need to relax the result.
     *
     * After our linearization, the only types of constraints we have are:
     * 1) monomial - slack = 0
     * 2) linear_polynomial ~ 0, where ~ is <=, =, >=, <, > (we assume it is <= or <)
     *
     * So the only time the constraint can be something different than an equality, it is a linear constraint.
     * This makes adjustment of the result for linear_polynomial = 0 to linear_polynomial ~ 0 easier.
     * If the relation was <= (taking the coefficient of the variable we solved for into account),
     * then the result will be relaxed to: (-inf, upper bound].
     * Similarly, if the relation was >=, then the result will be relaxed to [lower bound, inf)
     */
    if (mConstraint.relation() == carl::Relation::LEQ || mConstraint.relation() == carl::Relation::LESS) {
      // we want the coefficient of our variable, which always has degree 1 since it is a linear polynomial
      auto coefficient = mConstraint.coefficient(mVariable, 1).constantPart();
      carl::BoundType boundType = (mConstraint.relation() == carl::Relation::LEQ) ? carl::BoundType::WEAK : carl::BoundType::STRICT;

      if (coefficient > 0) {
        // the constraint is truly a <= or < relation
        // so we take (-inf, upper bound]
        resultA = IntervalT(0.0, carl::BoundType::INFTY, resultA.upper(), boundType);
        // we can ignore resultB, since linear polynomials will never lead to two intervals
      }
      else {
        // the constraint is actually a >= or > relation
        // so we take [lower bound, inf)
        resultA = IntervalT(resultA.lower(), boundType, 0.0, carl::BoundType::INFTY);
        // we can ignore resultB, since linear polynomials will never lead to two intervals
      }
    }
    else {
      // we assume all constraints are in the form: <= or =
      // so there is nothing to do here.
    }

    // finally, we intersect the contracted interval with the original interval
    IntervalT originalInterval = _bounds.getDoubleInterval(mVariable);
    resultA = resultA.intersect(originalInterval);
    resultB = resultB.intersect(originalInterval);

    if(split){ //Interval was split in two
      retB = resultB;
    } else { //only resultA

    }

    OneOrTwo<IntervalT> ret(resultA,retB);
    return ret;
  }
}
