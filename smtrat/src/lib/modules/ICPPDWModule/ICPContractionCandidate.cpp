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
      //TODO: Looking at all these cases is extremely tedious! This version ignores bounds that contain INFTY
      if(originalInterval.lowerBoundType() == carl::BoundType::INFTY
          || resultA.lowerBoundType() == carl::BoundType::INFTY
          || originalInterval.upperBoundType() == carl::BoundType::INFTY
          || resultA.upperBoundType() == carl::BoundType::INFTY){
        //resultA = IntervalT::unboundedInterval();
        resultA = originalInterval;
        resultB = IntervalT::emptyInterval();
      }
      else {
        // TODO: check if correct
        switch(mRelation){
          case carl::Relation::LEQ:
            if(originalInterval.lower() >= resultA.upper()){
              resultA = IntervalT::emptyInterval();
            } else {
              resultA = IntervalT(originalInterval.lower(),carl::BoundType::WEAK,(originalInterval.upper() <= resultA.upper()?originalInterval.upper():resultA.upper()),carl::BoundType::WEAK);
            }
            break;
          case carl::Relation::LESS:
            resultA = IntervalT(originalInterval.lower(),carl::BoundType::WEAK,(originalInterval.upper() <= resultA.upper()?originalInterval.upper():resultA.upper()),carl::BoundType::WEAK);
            break;
          case carl::Relation::GEQ:
            resultA = IntervalT((originalInterval.lower() >= resultA.lower()?originalInterval.lower():resultA.lower()),carl::BoundType::WEAK, originalInterval.upper(),carl::BoundType::WEAK);
            break;
          case carl::Relation::GREATER:
            if(originalInterval.upper() <= resultA.lower()){
              resultA = IntervalT::emptyInterval();
            } else {
              resultA = IntervalT((originalInterval.lower() >= resultA.lower()?originalInterval.lower():resultA.lower()),carl::BoundType::WEAK, originalInterval.upper(),carl::BoundType::WEAK);
            }
            break;
          default:
            cout << "This should not happen" << endl;
            cout << mVariable << "," << mConstraint << endl;
            break;
        }
      }
    }

    std::experimental::optional<IntervalT> retB;
    if (split) {
      retB = resultB;
      //SMTRAT_LOG_INFO("smtrat.module","Used " << *this << "\t to contract from " << originalInterval << "\t to " << resultA << " and " << resultB);
    }
    else {
      //SMTRAT_LOG_INFO("smtrat.module","Used " << *this << "\t to contract from " << originalInterval << "\t to " << resultA);
    }

    OneOrTwo<IntervalT> ret(resultA,retB);
    return ret;
  }
}
