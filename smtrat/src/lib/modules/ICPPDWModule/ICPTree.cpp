#include "ICPTree.h"
#include "ICPUtil.h"
#include "ICPPDWModule.h"

namespace smtrat
{

  template<class Settings>
  ICPTree<Settings>::ICPTree(std::set<carl::Variable>* originalVariables,ICPPDWModule<Settings>* module) :
    mOriginalVariables(originalVariables),
    mCurrentState(originalVariables,this),
    mParentTree(),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mConflictingVariables(),
    mIsUnsat(false),
    mActiveSimpleBounds(),
    mModule(module)
  {
  }

    template<class Settings>
  ICPTree<Settings>::ICPTree(ICPTree<Settings>* parent, const ICPState<Settings>& parentState,
    std::set<carl::Variable>* originalVariables, const std::set<ConstraintT>& simpleBounds,ICPPDWModule<Settings>* module) :
    mOriginalVariables(originalVariables),
    mCurrentState(parentState,originalVariables,this),
    mParentTree(parent),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mConflictingVariables(),
    mIsUnsat(false),
    mActiveSimpleBounds(simpleBounds),
    mModule(module)
  {
    // we need to actually add all the simple bounds to our new icp state
    for (const ConstraintT& simpleBound : mActiveSimpleBounds) {
      mCurrentState.addSimpleBound(simpleBound);
    }
  }


  template<class Settings>
  void ICPTree<Settings>::printVariableBounds() {
#ifdef PDW_MODULE_DEBUG_1
    std::cout << "Variable bounds:" << std::endl;
    for (const auto& mapEntry : mCurrentState.getIntervalMap()) {
      if (!mapEntry.second.isInfinite()) {
        std::cout << mapEntry.first << " in " << mapEntry.second << std::endl;
      }
    }
    std::cout << std::endl;
#endif
  }

    template<class Settings>
  bool ICPTree<Settings>::contract(std::priority_queue<ICPContractionCandidate<Settings>*,std::vector<ICPContractionCandidate<Settings>*>,
             CompareCandidates<Settings>>& ccPriorityQueue,ICPPDWModule<Settings>* module) {
    while(true) {
      printVariableBounds();

      // first we need to make sure the bounds are still satisfiable
      // i.e. no variable has an empty interval
      if (mCurrentState.isConflicting()) {
        handleUnsat();
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "Bounds are conflicting!\nReasons: " << std::endl;
        for (const ConstraintT& c : mConflictingConstraints) {
          std::cout << c << std::endl;
        }
        std::cout << std::endl;
#endif
        // we will terminate, but we did not split the search space
        return false;
      }
      // if we met some other termination condition (e.g. target diameter reached
      else if (mCurrentState.isTerminationConditionReached()) {
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "Termination condition reached." << std::endl;
#endif
        // we will terminate, but we did not split the search space
        return false;
      }
      // we can contract
      else {

        // We have to pick the best contraction candidate that we want to apply
        // if we have nothing to contract, we cannot use this method
        if (ccPriorityQueue.empty()) {
          return false;
        }
        std::experimental::optional<ICPContractionCandidate<Settings>*> bestCC = mCurrentState.getBestContractionCandidate(ccPriorityQueue);

        if(bestCC) { //if a contraction candidate has been found proceed
          OneOrTwo<IntervalT> bounds = (*bestCC)->getContractedInterval(mCurrentState.getIntervalMap());
          if(bounds.second) {
            // We contracted to two intervals, so we need to split
            // but only if we haven't reached the maximal number of splits yet
            if(getNumberOfSplits() > Settings::maxSplitNumber) {
#ifdef PDW_MODULE_DEBUG_1
              std::cout << "Termination reached by maximal number of splits!" << std::endl;
#endif
              return false;
            }
            else {
#ifdef PDW_MODULE_DEBUG_1
              std::cout << "Split on " << (*bestCC)->getVariable() << " by " << bounds.first << " vs " << (*bounds.second) << std::endl;
#endif
              split((*bestCC)->getVariable());

              // we split the tree, now we need to apply the intervals for the children
              mLeftChild->getCurrentState().applyContraction ((*bestCC),  bounds.first );
              mRightChild->getCurrentState().applyContraction((*bestCC), *bounds.second);
              return true;
            }
          } else {
            // no split, we can simply apply the contraction to the current state
#ifdef PDW_MODULE_DEBUG_1
            std::cout << "Contract with " << (*(*bestCC)) << ", results in bounds: " << bounds.first << std::endl;
#endif
            mCurrentState.applyContraction((*bestCC), bounds.first);
          }
        }else{ //otherwise perform a split
#ifdef PDW_MODULE_DEBUG_1
          std::cout << "Start guessing model before split!" << std::endl;
#endif
          std::experimental::optional<Model> model= (*module).getSolution(this);
          //if we found a model, just terminate with false indicating that no split occurred
            if(model){
#ifdef PDW_MODULE_DEBUG_1
              std::cout << "Model guessed without split!" << std::endl;
#endif
              (*module).setModel((*model));
              mIsUnsat = false;
              return false;
            }
            else {
#ifdef SMTRAT_DEVOPTION_Statistics
      mModule->getStatistics()->increaseNumberOfSplits();
#endif
#ifdef PDW_MODULE_DEBUG_1
              //now it is not sat, thus we have to split further
              std::cout << "No model found." << std::endl;
#endif

              // check if maximum number of splits has been reached and terminate
              if(getNumberOfSplits() > Settings::maxSplitNumber) {
#ifdef PDW_MODULE_DEBUG_1
                std::cout << "Termination reached by maximal number of splits!" << std::endl;
#endif
                return false;
              }
              else {
                //First extract the best variable for splitting
                carl::Variable splittingVar = mCurrentState.getBestSplitVariable();
                IntervalT oldInterval = mCurrentState.getInterval(splittingVar);

                std::pair<IntervalT, IntervalT> newIntervals = ICPUtil<Settings>::splitInterval(oldInterval);
#ifdef PDW_MODULE_DEBUG_1
                std::cout << "Split on " << splittingVar << " with new intervals: "
                  << newIntervals.first << " and " << newIntervals.second << "\n" << std::endl;
#endif
                split(splittingVar);
                mLeftChild->getCurrentState().setInterval(splittingVar, newIntervals.first, ConstraintT()); // empty origin
                mRightChild->getCurrentState().setInterval(splittingVar, newIntervals.second, ConstraintT());
                return true;
              }
            }
        }
      }
    }
  }

  template<class Settings>
  ICPState<Settings>& ICPTree<Settings>::getCurrentState() {
    return mCurrentState;
  }

  template<class Settings>
  std::experimental::optional<ICPTree<Settings>*> ICPTree<Settings>::getParentTree() {
    return mParentTree;
  }

  template<class Settings>
  ICPTree<Settings>* ICPTree<Settings>::getLeftChild() {
    return mLeftChild.get();
  }

  template<class Settings>
  ICPTree<Settings>* ICPTree<Settings>::getRightChild() {
    return mRightChild.get();
  }

  template<class Settings>
  bool ICPTree<Settings>::isLeaf() {
    return (!mLeftChild && !mRightChild);
  }

  template<class Settings>
  vector<ICPTree<Settings>*> ICPTree<Settings>::getLeafNodes() {
    vector<ICPTree<Settings>*> leafNodes;
    if (isLeaf()) {
      leafNodes.push_back(this);
    }
    else {
      if (mLeftChild) {
        vector<ICPTree<Settings>*> leftLeafNodes = mLeftChild->getLeafNodes();
        leafNodes.insert(leafNodes.end(), leftLeafNodes.begin(), leftLeafNodes.end());
      }
      if (mRightChild) {
        vector<ICPTree<Settings>*> rightLeafNodes = mRightChild->getLeafNodes();
        leafNodes.insert(leafNodes.end(), rightLeafNodes.begin(), rightLeafNodes.end());
      }
    }

    return leafNodes;
  }

  template<class Settings>
  std::experimental::optional<carl::Variable> ICPTree<Settings>::getSplitDimension() {
    return mSplitDimension;
  }

  template<class Settings>
  std::set<ConstraintT>& ICPTree<Settings>::getConflictingConstraints() {
    return mConflictingConstraints;
  }

  template<class Settings>
  std::set<carl::Variable>& ICPTree<Settings>::getConflictingVariables() {
    return mConflictingVariables;
  }

  template<class Settings>
  bool ICPTree<Settings>::isUnsat() {
    return mIsUnsat;
  }

  template<class Settings>
  void ICPTree<Settings>::clearUnsat() {
    mIsUnsat = false;
    mConflictingVariables.clear();
    mConflictingConstraints.clear();
    if (mLeftChild) {
      mLeftChild->clearUnsat();
    }
    if (mRightChild) {
      mRightChild->clearUnsat();
    }
  }

  template<class Settings>
  void ICPTree<Settings>::split(carl::Variable var) {
    mSplitDimension = var;

    // we create two new search trees with copies of the original bounds
    mLeftChild  = make_unique<ICPTree<Settings>>(this, mCurrentState, mOriginalVariables, mActiveSimpleBounds, mModule);
    mRightChild = make_unique<ICPTree<Settings>>(this, mCurrentState, mOriginalVariables, mActiveSimpleBounds, mModule);
  }

  template<class Settings>
  void ICPTree<Settings>::handleUnsat() {
    mIsUnsat = true;

    // so we retrieve the set of conflicting constraints and add them to our state
    mConflictingVariables.clear();
    mConflictingConstraints.clear();
    mConflictingVariables.insert(mCurrentState.getConflictingVariable());
    generateConflictReasons();

    // we have determined that this ICP search tree is unsatisfiable
    // if this tree was the last child of the parent, then this could mean that
    // every child of the parent is unsat, and thus, the parent is unsat
    // if that is the case, we need to propagate and accumulate the conflicting reasons
    if (mParentTree) {
      (*mParentTree)->accumulateConflictReasons();
    }
  }

  template<class Settings>
  void ICPTree<Settings>::setBackendsUnsat(std::vector<FormulaSetT>& backendInfSubsets) {
    mIsUnsat = true;

    mConflictingVariables.clear();
    mConflictingConstraints.clear();

    for (auto& formulaSet : backendInfSubsets) {
      for (auto& formula : formulaSet) {
        if (formula.getType() == carl::FormulaType::CONSTRAINT) {
          mConflictingConstraints.insert(formula.constraint());
        }
      }
    }

    // conflicting variables are all variables occuring in conflicting constraints
    for (auto& c : mConflictingConstraints) {
      for (auto& v : c.variables()) {
        mConflictingVariables.insert(v);
      }
    }

#ifdef PDW_MODULE_DEBUG_1
    std::cout << "Conflicting constraints determined by the backend: " << mConflictingConstraints << std::endl;
#endif

    if (mParentTree) {
      (*mParentTree)->accumulateConflictReasons();
    }
  }

  template<class Settings>
  void ICPTree<Settings>::generateConflictReasons() {
    // we start with only the conflicting variable
    // and determine all involved constraints and variables

    // traverse the applied contraction candidates and generate the transitive closure
    for (int i = (int) mCurrentState.getAppliedContractionCandidates().size() - 1; i >= 0; i--) {
      ICPContractionCandidate<Settings>* it = (mCurrentState.getAppliedContractionCandidates())[(unsigned int) i];
      // if the variable that was contracted was involved in the unsat reason, all the variables of the contractor are too
      if (mConflictingVariables.count(it->getVariable()) > 0) {
        // the constraint itself is an involved constraint
        // or it contains an involved variable
        auto cVars = it->getConstraint().variables();

        mConflictingVariables.insert(cVars.begin(), cVars.end());
        mConflictingConstraints.insert(it->getConstraint());
      }
    }

    // and we need to add all used simple bounds
    // we need to do this manually here, because the search tree never "contracts" with simple bounds
    // and thus, they will not appear in its conflicting constraint set
    for (const ConstraintT& c : mActiveSimpleBounds) {
      // we actually only need to add those simple bounds where the variable was used
      // during one of the contraction steps
      if (mConflictingVariables.count(*(c.variables().begin())) > 0) {
        mConflictingConstraints.insert(c);
      }
    }
  }

  template<class Settings>
  void ICPTree<Settings>::accumulateConflictReasons() {
    if (mLeftChild && mLeftChild->isUnsat() && mRightChild && mRightChild->isUnsat()) {
      mIsUnsat = true;
      mConflictingConstraints.clear();
      std::set<ConstraintT> leftReasons = mLeftChild->getConflictingConstraints();
      std::set<ConstraintT> rightReasons = mRightChild->getConflictingConstraints();
      mConflictingConstraints.insert(leftReasons.begin(), leftReasons.end());
      mConflictingConstraints.insert(rightReasons.begin(), rightReasons.end());

      mConflictingVariables.clear();
      std::set<carl::Variable> leftConflictVars = mLeftChild->getConflictingVariables();
      std::set<carl::Variable> rightConflictVars = mRightChild->getConflictingVariables();
      mConflictingVariables.insert(leftConflictVars.begin(), leftConflictVars.end());
      mConflictingVariables.insert(rightConflictVars.begin(), rightConflictVars.end());

      // we accumulated the conflict reasons of the left and right child
      // and now we need to add the conflict reasons of this parent tree
      generateConflictReasons();

      // we need to accumulate further
      if (mParentTree) {
        (*mParentTree)->accumulateConflictReasons();
      }
    }
  }

  template<class Settings>
  int ICPTree<Settings>::getNumberOfSplits(){
    return getRoot()->getNumberOfSplitsRecursive();
  }

  template<class Settings>
  ICPTree<Settings>* ICPTree<Settings>::getRoot(){
    if(mParentTree) {
      return (*mParentTree)->getRoot();
    }
    return this;
  }

  template<class Settings>
  int ICPTree<Settings>::getNumberOfSplitsRecursive(){
    int ret = 0;
    if(mLeftChild&&mRightChild) {
      ret +=1;
    }
    if(mLeftChild) {
      ret +=(*mLeftChild).getNumberOfSplitsRecursive();
    }
    if(mRightChild) {
      ret +=(*mRightChild).getNumberOfSplitsRecursive();
    }
    return ret;
  }

  template<class Settings>
  bool ICPTree<Settings>::addConstraint(const ConstraintT& _constraint) {
    // clear previous conflict results
    clearUnsat();

    // we can only directly add simple constraints to our variable bounds,
    // all other constraints will be handled by ICPPDWModule through mActiveContractionCandidates
    if (ICPUtil<Settings>::isSimpleBound(_constraint)) {
      mActiveSimpleBounds.insert(_constraint);
      mCurrentState.addSimpleBound(_constraint);

      // we need to add the constraint to all children as well
      // otherwise the leaf nodes will not know about the new constraint
      bool isLeftConflicting = false;
      if (mLeftChild) {
        isLeftConflicting = !mLeftChild->addConstraint(_constraint);
      }

      bool isRightConflicting = false;
      if (mRightChild) {
        isRightConflicting = !mRightChild->addConstraint(_constraint);
      }

      if (isLeftConflicting && isRightConflicting) {
        accumulateConflictReasons();
        return false;
      }
      else if (mCurrentState.isConflicting()) {
        // the added constraint yields an unsat search tree
        // directly for this current node
        handleUnsat();
        return false;
      }
      else {
        return true;
      }
    }
    else {
      return true;
    }
  }

  template<class Settings>
  void ICPTree<Settings>::removeConstraint(const ConstraintT& _constraint, std::set<carl::Variable> involvedVars, std::set<ConstraintT> involvedConstraints) {
    // clear previous conflict results
    clearUnsat();

    // remove the actual bound from the variable bounds
    if (ICPUtil<Settings>::isSimpleBound(_constraint)) {
      mActiveSimpleBounds.erase(_constraint);
      mCurrentState.removeSimpleBound(_constraint);
    }

    // check applied contraction candidates for involvment with the constraint that should be removed
    for (int i = 0; i < (int) mCurrentState.getAppliedContractionCandidates().size(); i++) {
      ICPContractionCandidate<Settings>* ccIt = (mCurrentState.getAppliedContractionCandidates())[(unsigned int) i];
      if (involvedConstraints.count(ccIt->getConstraint()) > 0 ||
          ICPUtil<Settings>::occurVariablesInConstraint(involvedVars, ccIt->getConstraint())) {
        // the constraint itself is an involved constraint
        // or it contains an involved variable
        involvedVars.insert(ccIt->getVariable());
        involvedConstraints.insert(ccIt->getConstraint());

        // now we need to revert and remove the applied contraction candidate
        mCurrentState.removeAppliedContraction((unsigned int) i);
        // since we remove one of them, our iterator is decreased by one
        i--;
      }
    }

    bool isLeftUnsat = false;
    bool isRightUnsat = false;

    // we need to delete the children if the splitting variable was an involved variable
    if (involvedVars.count(*mSplitDimension) > 0) {
      mLeftChild.reset();
      mRightChild.reset();
      mSplitDimension = std::experimental::nullopt;
    }
    else {
      // split was unrelated to the constraint that was removed, so remove the constraint from the children
      if (mLeftChild) {
        mLeftChild->removeConstraint(_constraint, involvedVars, involvedConstraints);
        isLeftUnsat = mLeftChild->isUnsat();
      }

      if (mRightChild) {
        mRightChild->removeConstraint(_constraint, involvedVars, involvedConstraints);
        isRightUnsat = mRightChild->isUnsat();
      }
    }

    // removal of this bound might have made this state sat again
    if (isLeftUnsat && isRightUnsat) {
      accumulateConflictReasons();
    }
    else if (mCurrentState.isConflicting()) {
      // reconstruct the unsat set
      handleUnsat();
    }
  }

  template<class Settings>
  void ICPTree<Settings>::removeConstraint(const ConstraintT& _constraint) {
    std::set<carl::Variable> vars;
    std::set<ConstraintT> cs;

    if (ICPUtil<Settings>::isSimpleBound(_constraint)) {
      // add the only involved variable in a simple bound
      vars.insert(*_constraint.variables().begin());
    }
    else {
      // it's not a simple bound, so we set the constraint itself as involved
      cs.insert(_constraint);
    }

    removeConstraint(_constraint, vars, cs);
  }

  template<class Settings>
  ICPPDWModule<Settings>* ICPTree<Settings>::getCorrespondingModule(){
    return mModule;
  }

  /**
   * Required in order to provide the priority queue with an ordering.
   * @param node1 the first compared node
   * @param node2 the second compared node
   * @return true if node1 fulfills less constraints than node2
   */
  template<class Settings>
  bool ICPTree<Settings>::compareTrees(ICPTree<Settings>* node1, ICPTree<Settings>* node2) {
    map<carl::Variable,double> sol(node1->getCurrentState().guessSolution());
    int numThis = 0;
    Model model;
    for(auto& clause : sol) {
      Rational val = carl::rationalize<Rational>(clause.second);
      model.emplace(clause.first, val);
    }
    for( const auto& rf : node1->getCorrespondingModule()->rReceivedFormula() ) {
      unsigned isSatisfied = carl::model::satisfiedBy(rf.formula().constraint(), model);
      assert(isSatisfied != 2);
      if(isSatisfied == 1) {
        numThis++;
      }
    }
    map<carl::Variable,double> sol2(node2->getCurrentState().guessSolution());
    int numThat = 0;
    Model model2;
    for(auto& clause : sol2) {
      Rational val = carl::rationalize<Rational>(clause.second);
      model2.emplace(clause.first, val);
    }
    for( const auto& rf : node1->getCorrespondingModule()->rReceivedFormula() ) {
      unsigned isSatisfied = carl::model::satisfiedBy(rf.formula().constraint(), model2);
      assert(isSatisfied != 2);
      if(isSatisfied == 1) {
        numThat++;
      }
    }
    return numThis<numThat;
  }

  //Template instantiations
  template class ICPTree<ICPPDWSettingsDebug>;
  template class ICPTree<ICPPDWSettingsProduction>;

}
