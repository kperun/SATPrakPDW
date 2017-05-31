#include "ICPContractionCandidate.h"

namespace smtrat
{
  ICPContractionCandidate::ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint):
    mVariable(var),
    mConstraint(constraint),
    mSolutionFormula(constraint.lhs(), var),
    mRelation(constraint.relation())
  {
    // we need to flip the relation if the coefficient is negative in a non-eq setting
    if (mConstraint.relation() != carl::Relation::EQ) {
      // get the coefficient of var in the constraint polynomial
      auto coefficient = mConstraint.coefficient(mVariable, 1).constantPart();

      if (coefficient < 0) {
        if(mConstraint.relation() == carl::Relation::LEQ){
          mRelation = carl::Relation::GEQ;
        } else if(mConstraint.relation() == carl::Relation::LESS) {
          mRelation = carl::Relation::GREATER;
        } else if(mConstraint.relation() == carl::Relation::GEQ) {
          mRelation = carl::Relation::LEQ;
        } else if(mConstraint.relation() == carl::Relation::GREATER) {
          mRelation = carl::Relation::LESS;
        }
      }
    }
  }

  carl::Variable ICPContractionCandidate::getVariable() {
    return mVariable;
  }

  ConstraintT& ICPContractionCandidate::getConstraint() {
    return mConstraint;
  }

  double ICPContractionCandidate::getWeight(){
    return mWeight;
  }

  void ICPContractionCandidate::setWeight(double weight){
    mWeight = weight;
  }

  OneOrTwo<IntervalT> ICPContractionCandidate::getContractedInterval(const vb::VariableBounds<ConstraintT>& _bounds) {
    // possible are two intervals resulting from a split
    IntervalT originalInterval = _bounds.getDoubleInterval(mVariable);
    IntervalT resultA = IntervalT::emptyInterval();
    IntervalT resultB = IntervalT::emptyInterval();
    bool split = false;

    // evaluate the solution formula
    std::vector<IntervalT> resultPropagation = mSolutionFormula.evaluate(_bounds.getIntervalMap());

    // the contraction was done on an equality
    if (mRelation == carl::Relation::EQ) {
      if (resultPropagation.size() == 0) {
        split = false;
        resultA = IntervalT::emptyInterval();
      }
      else if (resultPropagation.size() == 1) {
        split = false;
        resultA = resultPropagation[0];
        resultA = resultA.intersect(originalInterval);
      }
      else if (resultPropagation.size() == 2) {
        split = true;
        resultA = resultPropagation[0];
        resultA = resultA.intersect(originalInterval);
        resultB = resultPropagation[1];
        resultB = resultB.intersect(originalInterval);

        // a bit of cleanup: if one of them is empty, just take the other one
        if (resultB.isEmpty()) {
          split = false;
        }
        else if(resultA.isEmpty()) {
          resultA = resultB;
          resultB = IntervalT::emptyInterval();
          split = false;
        }
      }
      else {
        assert(false);
        cout << "ERROR: More than two interval results in solution formula for " << *this << endl;
      }
    }

    // the contraction was done on a inequality, so we need to fix the boundaries
    else {
      resultA = resultPropagation[0];
      split = false;

      //Next use the cases seen in slide 18 on ICP
      //Make the INFTY case easier by replacing one bound by INFTY
      switch(mRelation){
        case carl::Relation::LESS:
          if(resultA.upperBoundType() != carl::BoundType::INFTY && 
             originalInterval.lowerBoundType() != carl::BoundType::INFTY && 
             originalInterval.lower() >= resultA.upper()){
            resultA = IntervalT::emptyInterval();
          } else {
            resultA.setLowerBound(resultA.lower(),carl::BoundType::INFTY);
            resultA = resultA.intersect(originalInterval);
          }
          break;
        case carl::Relation::LEQ:
          resultA.setLowerBound(resultA.lower(),carl::BoundType::INFTY);
          resultA = resultA.intersect(originalInterval);
          break;
        case carl::Relation::GEQ:
          resultA.setUpperBound(resultA.upper(),carl::BoundType::INFTY);
          resultA = resultA.intersect(originalInterval);
          break;
        case carl::Relation::GREATER:
          if(originalInterval.upperBoundType() != carl::BoundType::INFTY &&
             resultA.lowerBoundType() != carl::BoundType::INFTY &&
             originalInterval.upper() <= resultA.lower()){
            resultA = IntervalT::emptyInterval();
          } else {
            resultA.setUpperBound(resultA.upper(),carl::BoundType::INFTY);
            resultA = resultA.intersect(originalInterval);
          }
          break;
        default:
          cout << "This should not happen" << endl;
          cout << mVariable << "," << mConstraint << endl;
          break;
      }
      resultB = IntervalT::emptyInterval();
    }

    std::experimental::optional<IntervalT> retB;
    if (split) {
      retB = resultB;
    }

    OneOrTwo<IntervalT> ret(resultA,retB);
    return ret;
  }
}
