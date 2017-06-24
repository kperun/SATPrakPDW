#include "ICPState.h"
#include "ICPContractionCandidate.h"
#include "ICPTree.h"
#include "ICPPDWModule.h"
#include "ICPUtil.h"
#include "../../logging.h"

namespace smtrat
{

  template<class Settings>
  ICPState<Settings>::ICPState(std::set<carl::Variable>* originalVariables,ICPTree<Settings>* correspondingTree) :
    mOriginalVariables(originalVariables),
    mCorrespondingTree(correspondingTree),
    mBounds(),
    mAppliedContractionCandidates(),
    mAppliedIntervalConstraints()
  {
  }

  template<class Settings>
  ICPState<Settings>::ICPState(const ICPState<Settings>& parentState, std::set<carl::Variable>* originalVariables, ICPTree<Settings>* correspondingTree) :
    mOriginalVariables(originalVariables),
    mCorrespondingTree(correspondingTree),
    mBounds(),
    mAppliedContractionCandidates(),
    mAppliedIntervalConstraints()
  {
    // copy parent's bounds to mBounds
    for (const auto& mapEntry : parentState.getIntervalMap()) {
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
  void ICPState<Settings>::initVariables(std::set<carl::Variable> vars) {
    for (const auto& v : vars) {
      // this getter will create an unbounded interval for unknown vars
      // so essentially, it is an initializer
      mBounds.getDoubleInterval(v);
    }
  }

  template<class Settings>
  void ICPState<Settings>::applyContraction(ICPContractionCandidate<Settings>* cc, IntervalT interval) {
    OneOrTwo<ConstraintT> intervalConstraints = setInterval(cc->getVariable(), interval, cc->getConstraint());
    addAppliedIntervalConstraint(intervalConstraints);
    addAppliedContractionCandidate(cc);
  }

  template<class Settings>
  OneOrTwo<ConstraintT> ICPState<Settings>::setInterval(carl::Variable var, const IntervalT& interval, const ConstraintT& _origin) {
    OneOrTwo<ConstraintT> constraints = ICPUtil<Settings>::intervalToConstraint(var, interval);
    mBounds.addBound(constraints.first, _origin);
    if (constraints.second) {
      mBounds.addBound(*(constraints.second), _origin);
    }
    return constraints;
  }

  template<class Settings>
  IntervalT ICPState<Settings>::getInterval(carl::Variable var) {
    return mBounds.getDoubleInterval(var);
  }

  template<class Settings>
  const EvalDoubleIntervalMap& ICPState<Settings>::getIntervalMap() const {
    return mBounds.getIntervalMap();
  }

  template<class Settings>
  vector<ICPContractionCandidate<Settings>*>& ICPState<Settings>::getAppliedContractionCandidates() {
    return mAppliedContractionCandidates;
  }

  template<class Settings>
  void ICPState<Settings>::addAppliedContractionCandidate(ICPContractionCandidate<Settings>* contractionCandidate) {
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
  void ICPState<Settings>::addSimpleBound(const ConstraintT& simpleBound) {
    mBounds.addBound(simpleBound, ConstraintT());
  }

  template<class Settings>
  void ICPState<Settings>::removeSimpleBound(const ConstraintT& simpleBound) {
    mBounds.removeBound(simpleBound, ConstraintT());
  }

  template<class Settings>
  void ICPState<Settings>::removeAppliedContraction(unsigned int index) {
    // first revert the interval constraints from the variable bounds
    removeIntervalConstraints(mAppliedIntervalConstraints[index], mAppliedContractionCandidates[index]->getConstraint());

    // then remove the entries from the member vectors
    mAppliedContractionCandidates.erase(mAppliedContractionCandidates.begin() + index);
    mAppliedIntervalConstraints.erase(mAppliedIntervalConstraints.begin() + index);
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

    //otherwise check if we have reached our desired interval
    //first check if all intervals are inside the desired one
    bool isTargetDiameterReached = true;
    for (auto key : (*mOriginalVariables) ) {
      if(getInterval(key).isUnbounded() || getInterval(key).diameter()>Settings::targetDiameter) {
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
  bool ICPState<Settings>::isConflicting() {
    return mBounds.isConflicting();
  }

  template<class Settings>
  void ICPState<Settings>::initializeWeights(std::vector<ICPContractionCandidate<Settings>*>& candidates){
    if(candidates.empty()) {
      return;
      }

    //for all handed over candidates initialize the weights
    for (int it = 0; it < (int) candidates.size(); it++) {
      // this wight has yet not been initialized
      if((*candidates[it]).getWeight()==-1){
        double currentGain = (candidates[it])->computeGain(getIntervalMap());
        //compute the weighted gain
        double currentGainWeighted = (*(candidates[it])).getWeight()+
                Settings::alpha*(currentGain-(*(candidates[it])).getWeight());
        //now set this value as the init weight
        (*(candidates[it])).setWeight(currentGainWeighted);
      }else{// otherwise it is already initialized, thus scale them a little
        (*(candidates[it])).setWeight((*(candidates[it])).getWeight()*Settings::updateFactor);
      }
    }
  }


  template<class Settings>
  std::experimental::optional<ICPContractionCandidate<Settings>*> ICPState<Settings>::getBestContractionCandidate(
    std::priority_queue<ICPContractionCandidate<Settings>*,std::vector<ICPContractionCandidate<Settings>*>,
             CompareCandidates<Settings>>& ccPriorityQueue){
    //If the list is empty something must have gone wrong, since it was not empty in ICPTree
    if(ccPriorityQueue.empty()) {
      throw std::invalid_argument( "Candidates priority queue is empty!" );
    }

    //This vector keeps track of the elements that were popped from the queue
    std::vector<ICPContractionCandidate<Settings>*> poppedCandidates;

    //store the current best candidate index
    ICPContractionCandidate<Settings>* currentBest = ccPriorityQueue.top();
    ccPriorityQueue.pop(); //Pop so that the updated weight is used for sorting
    std::experimental::optional<double> currentBestGain = currentBest->computeGain(getIntervalMap());

     //store the new diameter in case two candidates with equal gain are regarded
    double currentBestAbsoluteReduction = (*currentBestGain)*(getInterval((*currentBest).getVariable()).diameter());


    //first compute the new weighted gain according to W_new = W_old + alpha*(gain - W_old)
    double currentBestGainWeighted = (*currentBest).getWeight()+
              Settings::alpha * ( (*currentBestGain) - currentBest->getWeight() );
    //update the weight
    (*currentBest).setWeight(currentBestGainWeighted);

    //Store the element in the poppedCandidates vector
    poppedCandidates.push_back(currentBest);

    //Look at the first minCandidates -1 and choose the best one
    //We already looked at the first one
    for(int i = 1; i < Settings::minCandidates || currentBestGainWeighted <= Settings::weightEps; i++){
      //First retrieve and store the element
      //But check if the queue is already empty
      if(ccPriorityQueue.empty()){
        break; //We are done with this loop
      }
      ICPContractionCandidate<Settings>* currentElement = ccPriorityQueue.top();
      ccPriorityQueue.pop();
      poppedCandidates.push_back(currentElement);

      //Compute Gain and update weights
      double currentGain = currentElement->computeGain(getIntervalMap());
      //compute the weighted gain
      double currentGainWeighted = (*(currentElement)).getWeight()+
              Settings::alpha*(currentGain-(*(currentElement)).getWeight());
      //update the weighted gain
      (*(currentElement)).setWeight(currentGainWeighted);

      //do not consider candidates with weight < weight_eps
      if(currentBestGainWeighted<Settings::weightEps&&currentGainWeighted>Settings::weightEps){
        //if the previous candidate have not at lease epsilon weight, we disregard it
        currentBestGainWeighted = currentGainWeighted;
        currentBestGain = currentGain;
        currentBest = currentElement;
        //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
        currentBestAbsoluteReduction = currentGain*(getInterval((*(currentElement)).getVariable()).diameter());
        continue;
      }
      //if the current candidate is below weightEps, we disregard it
      if(currentGainWeighted<Settings::weightEps){
        continue;
      }
      //now actual comparison can take place
      //TODO: What? Why not always take the better one?
      if(currentGainWeighted-currentBestGainWeighted>Settings::upperDelta) {//the delta states that between the old and the new gain
        //the difference has to be at least upperDelta, by using this behavior we are able to enforce that only candidates which
        //achieve a certain margin of gain are regarded as the new optimal
        //now set the new best candidate as current
        currentBestGainWeighted = currentGainWeighted;
        currentBestGain = currentGain;
        currentBest = currentElement;
        //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
        currentBestAbsoluteReduction = currentGain*(getInterval((*(currentElement)).getVariable()).diameter());

        //TODO: Does it make more sense to look at best - current and say "It might be worse but the absolute gain is better"?
      }else if(currentGainWeighted-currentBestGainWeighted>Settings::lowerDelta){
        //if the gain is not high enough but still almost the same, it would be interesting to consider the absolute interval reduction
        double currentNewAbsoluteReduction = currentGain*(getInterval((*(currentElement)).getVariable()).diameter());
        //now check if the
        if(currentBestAbsoluteReduction<currentNewAbsoluteReduction){
           currentBestGainWeighted = currentGainWeighted;
           currentBestGain = currentGain;
           currentBest = currentElement;
           //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
           currentBestAbsoluteReduction = currentGain*(getInterval((*(currentElement)).getVariable()).diameter());
        }
      }

    }


    //Reinsert the popped elements at new positions
#ifdef PDW_MODULE_DEBUG_1
    std::cout << "Found and looked at " << poppedCandidates.size() << ", ignoring " << ccPriorityQueue.size() << " candidates!" << endl;
#endif
    for(int i = 0; i < poppedCandidates.size(); i ++){
      ccPriorityQueue.push(poppedCandidates[i]);
    }

    //Create the return optional
    std::experimental::optional<ICPContractionCandidate<Settings>*> ret;
    //Only return the object if the gain is good enough
    if(currentBestGainWeighted>Settings::weightEps){
      ret = currentBest;
      return ret;
    }else{
      return ret;
    }

/*
    for (int it = 1; it < (int) candidates.size(); it++) {
      double currentGain = (candidates[it])->computeGain(getIntervalMap());
      //compute the weighted gain
      double currentGainWeighted = (*(candidates[it])).getWeight()+
              Settings::alpha*(currentGain-(*(candidates[it])).getWeight());
      //update the weighted gain
      (*(candidates[it])).setWeight(currentGainWeighted);

      //do not consider candidates with weight < weight_eps
      if(currentBestGainWeighted<Settings::weightEps&&currentGainWeighted>Settings::weightEps){
        //if the previous candidate have not at lease epsilon weight, we disregard it
        currentBestGainWeighted = currentGainWeighted;
        currentBestGain = currentGain;
        currentBest = it;
        //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
        currentBestAbsoluteReduction = currentGain*(getInterval((*(candidates[it])).getVariable()).diameter());
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
        currentBestAbsoluteReduction = currentGain*(getInterval((*(candidates[it])).getVariable()).diameter());

      }else if(currentGainWeighted-currentBestGainWeighted>Settings::lowerDelta){
        //if the gain is not high enough but still almost the same, it would be interesting to consider the absolute interval reduction
        double currentNewAbsoluteReduction = currentGain*(getInterval((*(candidates[it])).getVariable()).diameter());
        //now check if the
        if(currentBestAbsoluteReduction<currentNewAbsoluteReduction){
           currentBestGainWeighted = currentGainWeighted;
           currentBestGain = currentGain;
           currentBest = it;
           //retrieve the new diameter by means of the formula D_old - (1-gain)*D_old = absolute reduction
           currentBestAbsoluteReduction = currentGain*(getInterval((*(candidates[it])).getVariable()).diameter());
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
    std::experimental::optional<unsigned int> ret;

    if((*currentBestGain) > Settings::gainThreshold) {
      //if the gain is beyond the threshold, return it
      ret = currentBest;
      return ret;
    }
    else{
      //otherwise return an optional.empty()
      return ret;
    }
*/

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
    std::vector<carl::Variable> unsatVars;
    Model model;

    //first collect all variables which are located in a unsat clause
    map<carl::Variable,double> sol(guessSolution());
     for(auto& clause : sol) {
        Rational val = carl::rationalize<Rational>(clause.second);
        model.emplace(clause.first, val);
      }
     for( const auto& rf : mCorrespondingTree->getCorrespondingModule()->rReceivedFormula()) {
       //fist check if this formula is sat
       unsigned isSatisfied = carl::model::satisfiedBy(rf.formula().constraint(), model);

       assert(isSatisfied != 2);
       if(isSatisfied != 1) {
          //if it is not sat, get the corresponding variables from the initial constraints
          for(const auto& var:rf.formula().constraint().variables()){
            if(std::find(unsatVars.begin(), unsatVars.end(), var) == unsatVars.end()) {
             //this var is not yet in the vector, add it
              unsatVars.push_back(var);
            }
          }
        }
      }
      carl::Variable bestSplitVariable = unsatVars[0];
    // now finally we can iterate over all variables which are part of an unsat clause
    for (carl::Variable var : unsatVars) {
      currentInterval = getInterval(var).diameter();
      //first compute the diameter of a variable
      if (getInterval(var).isUnbounded()) {
        return var;
      }
      //now check if the new interval is "bigger"
      else if(bestSplitInterval<currentInterval) {
        bestSplitVariable = var;
        bestSplitInterval = currentInterval;
      }
    }
    //finally return the variable of the biggest interval
    return bestSplitVariable;
  }

  //Template instantiations
  template class ICPState<ICPPDWSettingsDebug>;
  template class ICPState<ICPPDWSettingsProduction>;
};
