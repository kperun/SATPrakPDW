#include "ICPContractionCandidate.h"

namespace smtrat
{
  template<class Settings>
  ICPContractionCandidate<Settings>::ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint):
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

  template<class Settings>
  carl::Variable ICPContractionCandidate<Settings>::getVariable() {
    return mVariable;
  }

  template<class Settings>
  ConstraintT& ICPContractionCandidate<Settings>::getConstraint() {
    return mConstraint;
  }

  template<class Settings>
  double ICPContractionCandidate<Settings>::getWeight(){
    return mWeight;
  }

  template<class Settings>
  void ICPContractionCandidate<Settings>::setWeight(double weight){
    mWeight = weight;
  }

  template<class Settings>
  OneOrTwo<IntervalT> ICPContractionCandidate<Settings>::getContractedInterval(const EvalDoubleIntervalMap& intervalMap) {
    // get the original interval
    IntervalT originalInterval(0, carl::BoundType::INFTY, 0, carl::BoundType::INFTY);
    auto it = intervalMap.find(mVariable);
    if (it != intervalMap.end()) {
      originalInterval = it->second;
    }

    // possible are two intervals resulting from a split
    IntervalT resultA = IntervalT::emptyInterval();
    IntervalT resultB = IntervalT::emptyInterval();
    bool split = false;

    // evaluate the solution formula
    std::vector<IntervalT> resultPropagation = mSolutionFormula.evaluate(intervalMap);

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

    // the contraction was done on an inequality, so we need to fix the boundaries
    else {
      resultA = resultPropagation[0];
      split = false;

      // First case: restulA is empty. This means the rhs is already unsat, so we return the empty interval
      if(resultA.isEmpty()){
        resultA = IntervalT::emptyInterval();
      } else {

        // Next use the cases seen in slide 18 on ICP
        // Make the INFTY case easier by replacing one bound by INFTY
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
            cout << "Error: mRelation is neither EQ nor an inequality relation!" << endl;
            cout << mVariable << "," << mConstraint << endl;
            break;
        }
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

  template<class Settings>
  double ICPContractionCandidate<Settings>::computeGain(const EvalDoubleIntervalMap& intervalMap){
    //first compute the new interval
    OneOrTwo<IntervalT> intervals = getContractedInterval(intervalMap);
    //then retrieve the old one
    IntervalT old_interval(0, carl::BoundType::INFTY, 0, carl::BoundType::INFTY);
    auto it = intervalMap.find(mVariable);
    if (it != intervalMap.end()) {
      old_interval = it->second;
    }

    //in order to avoid manipulation of the existing objects, we work here with retrieved values
    //moreover, we use a bigM in order to be able to compute with -INF and INF
    double newFirstLower = 0;
    double newFirstUpper = 0;
    double newSecondLower = 0;
    double newSecondUpper = 0;
    double oldIntervalLower = 0;
    double oldIntervalUpper = 0;
    //first the mandatory first interval
    if(intervals.first.lowerBoundType()== carl::BoundType::INFTY) {
      newFirstLower = -Settings::bigM;
    }else{
      if(intervals.first.lowerBoundType()== carl::BoundType::WEAK) {
        newFirstLower = intervals.first.lower();
      }else{ //in case it is scrict, we add a small epsilon to make it better
        newFirstLower = intervals.first.lower() + Settings::epsilon;
      }
    }

    if(intervals.first.upperBoundType()== carl::BoundType::INFTY) {
      newFirstUpper = Settings::bigM;
    }else{
      if(intervals.first.upperBoundType()== carl::BoundType::WEAK) {
        newFirstUpper = intervals.first.upper();
      }else{
        newFirstUpper = intervals.first.upper() - Settings::epsilon;
      }
    }

    //now the second optional interval
    if(intervals.second) {
      if((*(intervals.second)).lowerBoundType()== carl::BoundType::INFTY) {
        newSecondLower = -Settings::bigM;
      }else{
        if((*(intervals.second)).lowerBoundType()== carl::BoundType::WEAK) {
          newSecondLower = (*(intervals.second)).lower();
        }else{
          newSecondLower = (*(intervals.second)).lower() + Settings::epsilon;
        }

      }
      if((*(intervals.second)).upperBoundType()== carl::BoundType::INFTY) {
        newSecondUpper = Settings::bigM;
      }else{
        if((*(intervals.second)).upperBoundType()== carl::BoundType::WEAK) {
          newSecondUpper = (*(intervals.second)).upper();
        }else{
          newSecondUpper = (*(intervals.second)).upper() - Settings::epsilon;
        }
      }
    }
    //finally the old interval
    if(old_interval.lowerBoundType()== carl::BoundType::INFTY) {
      oldIntervalLower = -Settings::bigM;
    }else{
      if(old_interval.lowerBoundType()== carl::BoundType::WEAK) {
        oldIntervalLower = old_interval.lower();
      }else{
        oldIntervalLower = old_interval.lower()+Settings::epsilon;
      }
    }

    if(old_interval.upperBoundType()== carl::BoundType::INFTY) {
      oldIntervalUpper = Settings::bigM;
    }else{
      if(old_interval.upperBoundType()== carl::BoundType::WEAK) {
        oldIntervalUpper = old_interval.upper();
      }else{
        oldIntervalUpper = old_interval.upper() - Settings::epsilon;
      }
    }

    //return the value
    double ret = 1 -(std::abs(newFirstUpper-newFirstLower)+std::abs(newSecondUpper-newSecondLower))/std::abs(oldIntervalUpper-oldIntervalLower);
    if(intervals.second){
      ret *= Settings::splitPenalty;
    }
    return ret;
  }

  //Template instantiations
  template class ICPContractionCandidate<ICPPDWSettingsDebug>;
  template class ICPContractionCandidate<ICPPDWSettingsProduction>;
}
