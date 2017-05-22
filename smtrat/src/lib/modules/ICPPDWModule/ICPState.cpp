#include "ICPState.h"
#include "ICPContractionCandidate.h"
#include "ICPTree.h"
#include "ICPPDWModule.h"
#include "../../logging.h"

namespace smtrat
{
  ICPState::ICPState(ICPTree* correspondingTree) :
    mOriginalVariables(),
    mBounds(),
    mAppliedContractionCandidates(),
    mAppliedIntervalConstraints(),
    mCorrespondingTree(correspondingTree)
  {
  }

  ICPState::ICPState(std::set<carl::Variable>* originalVariables,ICPTree* correspondingTree) :
    mOriginalVariables(originalVariables),
    mBounds(),
    mAppliedContractionCandidates(),
    mAppliedIntervalConstraints(),
    mCorrespondingTree(correspondingTree)
  {
  }

  ICPState::ICPState(const vb::VariableBounds<ConstraintT>& parentBounds,std::set<carl::Variable>* originalVariables,ICPTree* correspondingTree) :
    mBounds(),
    mAppliedContractionCandidates(),
    mAppliedIntervalConstraints(),
    mOriginalVariables(originalVariables),
    mCorrespondingTree(correspondingTree)
  {
    // copy parentBounds to mBounds
    for (const auto& mapEntry : parentBounds.getIntervalMap()) {
      carl::Variable var = mapEntry.first;
      IntervalT interval = mapEntry.second;

      // since the origins are stored in the parent bounds
      // we will restore them later (during getConflictReasons)
      // but since we need an origin, we simply take the first one
      ConstraintT origin = parentBounds.getOriginsOfBounds(var)[0];

      setInterval(var, interval, origin);
    }
  }

  vb::VariableBounds<ConstraintT>& ICPState::getBounds() {
    return mBounds;
  }

  void ICPState::applyContraction(ICPContractionCandidate* cc, IntervalT interval) {
    OneOrTwo<ConstraintT> intervalConstraints = setInterval(cc->getVariable(), interval, cc->getConstraint());
    addAppliedIntervalConstraint(intervalConstraints);
    addAppliedContractionCandidate(cc);
  }

  OneOrTwo<ConstraintT> ICPState::setInterval(carl::Variable var, const IntervalT& interval, const ConstraintT& _origin) {
    // since we cannot directly set the interval for a variable,
    // we will need to add two constraints. one for the lower and one for the upper bound
    // one advantage of this approach is that we can easily revert a contraction
    // by removing those constraints from the variable bounds

    ConstraintT upperBound;
    bool hasUpper = false;
    ConstraintT lowerBound;
    bool hasLower = false;

    // if upper bound is infty, the constraint is useless
    if (interval.upperBoundType() != carl::BoundType::INFTY) {
      // x <= upper bound
      // x - upper bound <= 0
      Poly upperPoly;
      upperPoly += var;
      upperPoly -= interval.upper();
      carl::Relation upperRelation = (interval.upperBoundType() == carl::BoundType::WEAK) ? carl::Relation::LEQ : carl::Relation::LESS;
      upperBound = ConstraintT(upperPoly, upperRelation);
      hasUpper = true;
      mBounds.addBound(upperBound, _origin);
    }

    // if lower bound is infty, the constraint is useless
    if (interval.lowerBoundType() != carl::BoundType::INFTY) {
      // x >= lower bound
      // lower bound - x <= 0
      Poly lowerPoly;
      lowerPoly -= var;
      lowerPoly += interval.lower();
      carl::Relation lowerRelation = (interval.lowerBoundType() == carl::BoundType::WEAK) ? carl::Relation::LEQ : carl::Relation::LESS;
      lowerBound = ConstraintT(lowerPoly, lowerRelation);
      hasLower = true;
      mBounds.addBound(lowerBound, _origin);
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

  IntervalT ICPState::getInterval(carl::Variable var) {
    mBounds.getInterval(var);
  }

  vector<ICPContractionCandidate*>& ICPState::getAppliedContractionCandidates() {
    return mAppliedContractionCandidates;
  }

  void ICPState::addAppliedContractionCandidate(ICPContractionCandidate* contractionCandidate) {
    mAppliedContractionCandidates.push_back(contractionCandidate);
  }

  vector<OneOrTwo<ConstraintT> >& ICPState::getAppliedIntervalConstraints() {
    return mAppliedIntervalConstraints;
  }

  void ICPState::addAppliedIntervalConstraint(const OneOrTwo<ConstraintT>& constraints) {
    mAppliedIntervalConstraints.push_back(constraints);
  }

  carl::Variable ICPState::getConflictingVariable() {
    for (const auto& mapEntry : mBounds.getIntervalMap()) {
      if (mapEntry.second.isEmpty()) {
        return mapEntry.first;
      }
    }

    assert(false);
    return carl::freshRealVariable();
  }

  bool ICPState::isTerminationConditionReached() {
    if(mAppliedContractionCandidates.size() > ICPPDWSettings1::maxContractions) {
      SMTRAT_LOG_INFO("smtrat.module","Termination reached by max iterations!\n");
      return true;
    }
    //otherwise check if we have reached our desired interval
    //first check if all intervals are inside the desired one
    for (auto key : (*mOriginalVariables) ) {
      if(mBounds.getDoubleInterval(key).diameter()>ICPPDWSettings1::targetDiameter) {
        return false;
      }

    }
    // no check if maximum number of splits has been reached and terminate
    if(computeNumberOfSplits()>ICPPDWSettings1::maxSplitNumber) {
      SMTRAT_LOG_INFO("smtrat.module","Termination reached by maximal number of splits!\n");
      return true;
    }

    //if all intervals are ok, just terminate
    SMTRAT_LOG_INFO("smtrat.module","Termination reached by desired interval diameter!\n");
    return true;


  }

  int ICPState::computeNumberOfSplits(){
    return mCorrespondingTree->getNumberOfSplits();
  }

  double ICPState::computeGain(smtrat::ICPContractionCandidate& candidate,vb::VariableBounds<ConstraintT>& _bounds){
    //first compute the new interval
    OneOrTwo<IntervalT> intervals = candidate.getContractedInterval(_bounds);
    //then retrieve the old one
    IntervalT old_interval = _bounds.getDoubleInterval(candidate.getVariable());

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
      newFirstLower = -ICPPDWSettings1::bigM;
    }else{
      if(intervals.first.lowerBoundType()== carl::BoundType::WEAK) {
        newFirstLower = intervals.first.lower();
      }else{ //in case it is scrict, we add a small epsilon to make it better
        newFirstLower = intervals.first.lower() + ICPPDWSettings1::epsilon;
      }
    }

    if(intervals.first.upperBoundType()== carl::BoundType::INFTY) {
      newFirstUpper = ICPPDWSettings1::bigM;
    }else{
      if(intervals.first.upperBoundType()== carl::BoundType::WEAK) {
        newFirstUpper = intervals.first.upper();
      }else{
        newFirstUpper = intervals.first.upper() - ICPPDWSettings1::epsilon;
      }
    }

    //now the second optional interval
    if(intervals.second) {
      if((*(intervals.second)).lowerBoundType()== carl::BoundType::INFTY) {
        newSecondLower = -ICPPDWSettings1::bigM;
      }else{
        if((*(intervals.second)).lowerBoundType()== carl::BoundType::WEAK) {
          newSecondLower = (*(intervals.second)).lower();
        }else{
          newSecondLower = (*(intervals.second)).lower() + ICPPDWSettings1::epsilon;
        }

      }
      if((*(intervals.second)).upperBoundType()== carl::BoundType::INFTY) {
        newSecondUpper = ICPPDWSettings1::bigM;
      }else{
        if((*(intervals.second)).upperBoundType()== carl::BoundType::WEAK) {
          newSecondUpper = (*(intervals.second)).upper();
        }else{
          newSecondUpper = (*(intervals.second)).upper() - ICPPDWSettings1::epsilon;
        }
      }
    }
    //finally the old interval
    if(old_interval.lowerBoundType()== carl::BoundType::INFTY) {
      oldIntervalLower = -ICPPDWSettings1::bigM;
    }else{
      if(old_interval.lowerBoundType()== carl::BoundType::WEAK) {
        oldIntervalLower = old_interval.lower();
      }else{
        oldIntervalLower = old_interval.lower()+ICPPDWSettings1::epsilon;
      }
    }

    if(old_interval.upperBoundType()== carl::BoundType::INFTY) {
      oldIntervalUpper = ICPPDWSettings1::bigM;
    }else{
      if(old_interval.upperBoundType()== carl::BoundType::WEAK) {
        oldIntervalUpper = old_interval.upper();
      }else{
        oldIntervalUpper = old_interval.upper() - ICPPDWSettings1::epsilon;
      }
    }

    //return the value
    return 1 -(std::abs(newFirstUpper-newFirstLower)+std::abs(newSecondUpper-newSecondLower))/std::abs(oldIntervalUpper-oldIntervalLower);
  }

  std::experimental::optional<int> ICPState::getBestContractionCandidate(vector<ICPContractionCandidate*>& candidates){
    if(candidates.size()==0) {
      throw std::invalid_argument( "Candidates vector is empty!" );
    }
    //in the case that the list has only one element, return this one element
    if(candidates.size()==1) {
      return 0; //return the first element
    }
    //store the current best candidate index
    int currentBest = 0;
    std::experimental::optional<double> currentBestGain = computeGain(*(candidates[currentBest]),mBounds);
    for (int it = 1; it < (int) candidates.size(); it++) {
      double currentGain = computeGain(*(candidates[it]), mBounds);
      if(currentGain>currentBestGain) {
        //now set the new best candidate as current
        currentBestGain = currentGain;
        currentBest = it;
      }
    }

    std::experimental::optional<int> ret;


    if(currentBestGain>ICPPDWSettings1::gainThreshold) {
      //if the gain is beyond the threshold, return it
      ret = currentBest;
      return ret;
    }
    else{
      //otherwise return an optional.empty()
      return ret;
    }

  }

  map<carl::Variable,double> ICPState::guessSolution(){
    map<carl::Variable,double> ret;
    //TODO: This only checks the first of possibly several intervals?
    const EvalDoubleIntervalMap& bounds = mBounds.getIntervalMap();
    for(auto& bound : bounds) {
      double mid = 0; //Default if something goes wrong
      double epsilon = ICPPDWSettings1::epsilon;
      if(bound.second.isEmpty()) { //No values in interval, should not happen
        mid = 0;
      } else if (bound.second.isInfinite()) { //Both are INFTY
        mid = 0;
      } else if (bound.second.isUnbounded()) { //Only one is INFTY
        if(bound.second.lowerBoundType() == carl::BoundType::INFTY) { //Has upper bound
          if(bound.second.upperBoundType() == carl::BoundType::STRICT) { //Upper bound is strict
            mid = bound.second.upper() - epsilon; //Subtract some small epsilon in this case
          } else {
            mid = bound.second.upper();
          }
        } else if(bound.second.upperBoundType() == carl::BoundType::INFTY) { //Has lower bound
          if(bound.second.lowerBoundType() == carl::BoundType::STRICT) { //lower bound is strict
            mid = bound.second.lower() - epsilon; //Subtract some small epsilon in this case
          } else {
            mid = bound.second.lower();
          }
        } else { //Should never happen
          mid = 0;
        }
      } else { //No INFTY
        mid = (bound.second.diameter()/ 2.0) + bound.second.lower();
      }
      ret.insert(std::pair<carl::Variable,double>(bound.first,mid));
    };

    return ret;

  }

  carl::Variable ICPState::getBestSplitVariable(vector<ICPContractionCandidate*>& candidates){
    OneOrTwo<IntervalT> intervals;
    double currentInterval = 0;
    double bestSplitInterval = 0;
    double bestSplitCandidate = 0;
    cout << "Splitting" << endl;

    for (int it = 0; it < (int) candidates.size(); it++) {
      if((*mOriginalVariables).find(candidates[it]->getVariable()) != (*mOriginalVariables).end()) {
        //first compute the diameter of a variable
        currentInterval = mBounds.getDoubleInterval(candidates[it]->getVariable()).diameter();
        //now check if the new interval is "bigger"
        if(bestSplitInterval<currentInterval) {
          bestSplitCandidate = it;
          bestSplitInterval = currentInterval;
        }
      }
    }

    //finally return the variable of the biggest interval
    return candidates[bestSplitCandidate]->getVariable();
  }


};
