#include "ICPState.h"
#include "ICPContractionCandidate.h"
#include "ICPTree.h"
#include "ICPPDWModule.h"
#include "ICPUtil.h"
#include "../../logging.h"

namespace smtrat
{
  template class ICPState<ICPPDWSettingsDebug>;
  template class ICPState<ICPPDWSettingsProduction>;


  template<class Settings>
  ICPState<Settings>::ICPState(ICPTree<Settings>* correspondingTree) :
    mOriginalVariables(),
    mBounds(),
    mAppliedContractionCandidates(),
    mAppliedIntervalConstraints(),
    mCorrespondingTree(correspondingTree)
  {
  }

  template<class Settings>
  ICPState<Settings>::ICPState(std::set<carl::Variable>* originalVariables,ICPTree<Settings>* correspondingTree) :
    mOriginalVariables(originalVariables),
    mBounds(),
    mAppliedContractionCandidates(),
    mAppliedIntervalConstraints(),
    mCorrespondingTree(correspondingTree)
  {
  }

  template<class Settings>
  ICPState<Settings>::ICPState(const vb::VariableBounds<ConstraintT>& parentBounds,std::set<carl::Variable>* originalVariables,ICPTree<Settings>* correspondingTree) :
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

      // if the interval is infinite, there is no point in setting it
      // (setInterval actually expects a bounded interval)
      if (!interval.isInfinite()) {
        setInterval(var, interval, ConstraintT());
      }
      else {
        // we also need to make sure the copied variable bounds object knows about unbounded variables
        // to this end, we will simply call "getDoubleInterval" on every unbounded variable once
        // this method call will emplace an unbounded interval for this variable in the variable bounds object
        mBounds.getDoubleInterval(var);
      }
    }
  }

  template<class Settings>
  vb::VariableBounds<ConstraintT>& ICPState<Settings>::getBounds() {
    return mBounds;
  }

  template<class Settings>
  void ICPState<Settings>::applyContraction(ICPContractionCandidate* cc, IntervalT interval) {
    OneOrTwo<ConstraintT> intervalConstraints = setInterval(cc->getVariable(), interval, cc->getConstraint());
    addAppliedIntervalConstraint(intervalConstraints);
    addAppliedContractionCandidate(cc);
  }

  template<class Settings>
  OneOrTwo<ConstraintT> ICPState<Settings>::setInterval(carl::Variable var, const IntervalT& interval, const ConstraintT& _origin) {
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

  template<class Settings>
  IntervalT ICPState<Settings>::getInterval(carl::Variable var) {
    mBounds.getInterval(var);
  }

  template<class Settings>
  vector<ICPContractionCandidate*>& ICPState<Settings>::getAppliedContractionCandidates() {
    return mAppliedContractionCandidates;
  }

  template<class Settings>
  void ICPState<Settings>::addAppliedContractionCandidate(ICPContractionCandidate* contractionCandidate) {
    mAppliedContractionCandidates.push_back(contractionCandidate);
  }

  template<class Settings>
  vector<OneOrTwo<ConstraintT> >& ICPState<Settings>::getAppliedIntervalConstraints() {
    return mAppliedIntervalConstraints;
  }

  template<class Settings>
  void ICPState<Settings>::addAppliedIntervalConstraint(const OneOrTwo<ConstraintT>& constraints) {
    mAppliedIntervalConstraints.push_back(constraints);
  }

  template<class Settings>
  bool ICPState<Settings>::removeConstraint(const ConstraintT& constraint) {
    // if we remove a constraint that has been used in this ICPState, all subsequent contractions become invalid
    // so we need to revert every applied contraction from the first application of the removed constraint
    int firstApplicationIndex = -1;
    bool isUsed = false;

    // a simple bound is not used as a contraction candidate, but simply applied to the bounds
    // thus, we assume that a simple bound is always used immediatly
    if (ICPUtil<Settings>::isSimpleBound(constraint)) {
      // basically, we need to revert all changes, since the very first contraction candidate
      // will already have made use of the simple bound
      firstApplicationIndex = 0;
      isUsed = true;
    }
    else {
      // we find the first usage of the removed constraint
      for (int i = 0; i < (int) mAppliedContractionCandidates.size(); i++) {
        if (mAppliedContractionCandidates[i]->getConstraint() == constraint) {
          firstApplicationIndex = i;
          isUsed = true;
          break;
        }
      }
    }

    // if it has not been used at all, we don't have to do anything
    if (!isUsed) {
      return false;
    }
    // the constraint has been used, so we traverse the applied contraction from the end
    // until the first application index, and revert all bound constraints that were applied
    else {
      for (int i = mAppliedIntervalConstraints.size() - 1; i >= firstApplicationIndex; i--) {
        removeIntervalConstraints(mAppliedIntervalConstraints[i], mAppliedContractionCandidates[i]->getConstraint());
      }
      // actually delete those applied entries from the vectors
      mAppliedContractionCandidates.resize(firstApplicationIndex);
      mAppliedIntervalConstraints.resize(firstApplicationIndex);
    }
  }

  template<class Settings>
  void ICPState<Settings>::removeIntervalConstraints(const OneOrTwo<ConstraintT>& intervalConstraints, const ConstraintT& origin) {
    const ConstraintT& constraint1 = intervalConstraints.first;
    mBounds.removeBound(constraint1, origin);

    if (intervalConstraints.second) {
      const ConstraintT& constraint2 = *(intervalConstraints.second);
      mBounds.removeBound(constraint2, origin);
    }
  }

  template<class Settings>
  carl::Variable ICPState<Settings>::getConflictingVariable() {
    for (const auto& mapEntry : mBounds.getIntervalMap()) {
      if (mapEntry.second.isEmpty()) {
        return mapEntry.first;
      }
    }

    assert(false);
    return carl::freshRealVariable();
  }

  template<class Settings>
  bool ICPState<Settings>::isTerminationConditionReached() {
    if(mAppliedContractionCandidates.size() > Settings::maxContractions) {
#ifdef PDW_MODULE_DEBUG_1
      std::cout << "Termination reached by max iterations!" << std::endl;
#endif
      return true;
    }

    // check if maximum number of splits has been reached and terminate
    if(computeNumberOfSplits()>Settings::maxSplitNumber) {
#ifdef PDW_MODULE_DEBUG_1
      std::cout << "Termination reached by maximal number of splits!" << std::endl;
#endif
      return true;
    }

    //otherwise check if we have reached our desired interval
    //first check if all intervals are inside the desired one
    bool isTargetDiameterReached = true;
    for (auto key : (*mOriginalVariables) ) {
      if(mBounds.getDoubleInterval(key).isUnbounded() || mBounds.getDoubleInterval(key).diameter()>Settings::targetDiameter) {
        isTargetDiameterReached = false;
        break;
      }
    }
    if (isTargetDiameterReached) {
      //if all intervals are ok, just terminate
#ifdef PDW_MODULE_DEBUG_1
      std::cout << "Termination reached by desired interval diameter!" << std::endl;
#endif
      return true;
    }

    return false;
  }

  template<class Settings>
  int ICPState<Settings>::computeNumberOfSplits(){
    return mCorrespondingTree->getNumberOfSplits();
  }

  template<class Settings>
  double ICPState<Settings>::computeGain(smtrat::ICPContractionCandidate& candidate,vb::VariableBounds<ConstraintT>& _bounds){
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
    return 1 -(std::abs(newFirstUpper-newFirstLower)+std::abs(newSecondUpper-newSecondLower))/std::abs(oldIntervalUpper-oldIntervalLower);
  }

  template<class Settings>
  std::experimental::optional<int> ICPState<Settings>::getBestContractionCandidate(vector<ICPContractionCandidate*>& candidates){
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

     //store the new diameter in case two candidates with equal gain are regarded
    double currentBestAbsoluteReduction = (*currentBestGain)*(mBounds.getDoubleInterval((*(candidates[currentBest])).getVariable()).diameter());


    //first compute the new weighted gain according to W_new = W_old + alpha*(gain - W_old)
    double currentBestGainWeighted = (*(candidates[currentBest])).getWeight()+
              Settings::alpha*((*currentBestGain)-(*(candidates[currentBest])).getWeight());
    //update the weight
    //SMTRAT_LOG_INFO("smtrat.module","Old weight of " << (*(candidates[currentBest]))<< " is " << (*(candidates[currentBest])).getWeight());
    (*(candidates[currentBest])).setWeight(currentBestGainWeighted);
    //SMTRAT_LOG_INFO("smtrat.module","Weight of " << (*(candidates[currentBest]))<< " adjusted to " << currentBestGainWeighted);

    for (int it = 1; it < (int) candidates.size(); it++) {
      double currentGain = computeGain(*(candidates[it]), mBounds);
      //compute the weighted gain
      double currentGainWeighted = (*(candidates[it])).getWeight()+
              Settings::alpha*(currentGain-(*(candidates[it])).getWeight());
      //update the weighted gain
      //SMTRAT_LOG_INFO("smtrat.module","Old weight of " << (*(candidates[it]))<< " is " << (*(candidates[it])).getWeight());
      (*(candidates[it])).setWeight(currentGainWeighted);
      //SMTRAT_LOG_INFO("smtrat.module","Weight of " << (*(candidates[it]))<< " adjusted to " << currentGainWeighted);

      //do not consider candidates with weight < weight_eps
      if(currentBestGainWeighted<Settings::weightEps&&currentGainWeighted>Settings::weightEps){
        //if the previous candidate have not at lease epsilon weight, we disregard it
        currentBestGainWeighted = currentGainWeighted;
        currentBestGain = currentGain;
        currentBest = it;
        //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
        currentBestAbsoluteReduction = currentGain*(mBounds.getDoubleInterval((*(candidates[it])).getVariable()).diameter());
        continue;
      }
      //if the current candidate is below weightEps, we disregard it
      if(currentGainWeighted<Settings::weightEps){
        continue;
      }
      //now actual comparison can take place
      if(currentGainWeighted-currentBestGainWeighted>Settings::upperDelta) {//the delta states that between the old and the new gain
        //the difference has to be at least upperDelta, by using this behavior we are able to enforce that only candidates which
        //achieve a certain margin of gain are regarded as the new optimal
        //now set the new best candidate as current
        currentBestGainWeighted = currentGainWeighted;
        currentBestGain = currentGain;
        currentBest = it;
        //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
        currentBestAbsoluteReduction = currentGain*(mBounds.getDoubleInterval((*(candidates[it])).getVariable()).diameter());

      }else if(currentGainWeighted-currentBestGainWeighted>Settings::lowerDelta){
        //if the gain is not high enough but still almost the same, it would be interesting to consider the absolute interval reduction
        double currentNewAbsoluteReduction = currentGain*(mBounds.getDoubleInterval((*(candidates[it])).getVariable()).diameter());
        //now check if the
        if(currentBestAbsoluteReduction<currentNewAbsoluteReduction){
           currentBestGainWeighted = currentGainWeighted;
           currentBestGain = currentGain;
           currentBest = it;
           //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
           currentBestAbsoluteReduction = currentGain*(mBounds.getDoubleInterval((*(candidates[it])).getVariable()).diameter());
        }
      }
    }
#ifdef SMTRAT_DEVOPTION_Statistics
    if(currentBestGain){
      mCorrespondingTree->getCorrespondingModule()->
        getStatistics()->addContractionGain((*currentBestGain));
       mCorrespondingTree->getCorrespondingModule()->
        getStatistics()->increaseNumberOfContractions();
    }
#endif
    std::experimental::optional<int> ret;

    if(currentBestGain>Settings::gainThreshold) {
      //if the gain is beyond the threshold, return it
      ret = currentBest;
      return ret;
    }
    else{
      //otherwise return an optional.empty()
      return ret;
    }

  }

  template<class Settings>
  map<carl::Variable,double> ICPState<Settings>::guessSolution(){
    map<carl::Variable,double> ret;
    //TODO: This only checks the first of possibly several intervals?
    const EvalDoubleIntervalMap& bounds = mBounds.getIntervalMap();
    for(auto& bound : bounds) {
      double mid = 0; //Default if something goes wrong
      double epsilon = Settings::epsilon;
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

  template<class Settings>
  carl::Variable ICPState<Settings>::getBestSplitVariable(){
    OneOrTwo<IntervalT> intervals;
    double currentInterval = 0;
    double bestSplitInterval = 0;
    carl::Variable bestSplitVariable;

    for (carl::Variable var : *mOriginalVariables) {
      //first compute the diameter of a variable
      currentInterval = mBounds.getDoubleInterval(var).diameter();
      //now check if the new interval is "bigger"
      if(bestSplitInterval<currentInterval) {
        bestSplitVariable = var;
        bestSplitInterval = currentInterval;
      }
    }

    //finally return the variable of the biggest interval
    return bestSplitVariable;
  }


};
