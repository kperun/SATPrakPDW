#include "ICPTree.h"
#include "ICPUtil.h"
#include "ICPPDWModule.h"

namespace smtrat
{

  template class ICPTree<ICPPDWSettingsDebug>;
  template class ICPTree<ICPPDWSettingsProduction>;

   template<class Settings>
  ICPTree<Settings>::ICPTree(ICPPDWModule<Settings>* module) :
    mCurrentState(this),
    mParentTree(),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mConflictingVariables(),
    mOriginalVariables(),
    mIsUnsat(false),
    mActiveSimpleBounds(),
    mModule(module)
  {
  }

  template<class Settings>
  ICPTree<Settings>::ICPTree(std::set<carl::Variable>* originalVariables,ICPPDWModule<Settings>* module) :
    mCurrentState(originalVariables,this),
    mParentTree(),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mConflictingVariables(),
    mOriginalVariables(originalVariables),
    mIsUnsat(false),
    mActiveSimpleBounds(),
    mModule(module)
  {
  }

    template<class Settings>
  ICPTree<Settings>::ICPTree(ICPTree<Settings>* parent, const vb::VariableBounds<ConstraintT>& parentBounds,
    std::set<carl::Variable>* originalVariables, const std::set<ConstraintT>& simpleBounds,ICPPDWModule<Settings>* module) :
    mCurrentState(parentBounds,originalVariables,this),
    mParentTree(parent),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mConflictingVariables(),
    mOriginalVariables(originalVariables),
    mIsUnsat(false),
    mActiveSimpleBounds(simpleBounds),
    mModule(module)
  {
    // we need to actually add all the simple bounds to our new icp state
    for (const ConstraintT& simpleBound : mActiveSimpleBounds) {
      mCurrentState.getBounds().addBound(simpleBound, simpleBound);
    }
  }


  template<class Settings>
  void ICPTree<Settings>::printVariableBounds() {
#ifdef PDW_MODULE_DEBUG_1
    std::cout << "Variable bounds:" << std::endl;
    for (const auto& mapEntry : mCurrentState.getBounds().getIntervalMap()) {
      if (!mapEntry.second.isInfinite()) {
        std::cout << mapEntry.first << " in " << mapEntry.second << std::endl;
      }
    }
    std::cout << std::endl;
#endif
  }

  template<class Settings>
  bool ICPTree<Settings>::contract(vector<ICPContractionCandidate*>& contractionCandidates,ICPPDWModule<Settings>* module) {
    while(true) {
      printVariableBounds();

      // first we need to make sure the bounds are still satisfiable
      // i.e. no variable has an empty interval
      if (mCurrentState.getBounds().isConflicting()) {
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
        if (contractionCandidates.empty()) {
          return false;
        }
        std::experimental::optional<int> bestCC = mCurrentState.getBestContractionCandidate(contractionCandidates);

        if(bestCC) { //if a contraction candidate has been found proceed
          OneOrTwo<IntervalT> bounds = contractionCandidates.at((*bestCC))->getContractedInterval(mCurrentState.getBounds());
          if(bounds.second) {
            // We contracted to two intervals, so we need to split
#ifdef PDW_MODULE_DEBUG_1
            std::cout << "Split on " << contractionCandidates.at((*bestCC))->getVariable() << " by " << bounds.first << " vs " << (*bounds.second) << std::endl;
#endif
            split(contractionCandidates.at((*bestCC))->getVariable());

            // we split the tree, now we need to apply the intervals for the children
            mLeftChild->getCurrentState().applyContraction(contractionCandidates.at((*bestCC)),  bounds.first );
            mRightChild->getCurrentState().applyContraction(contractionCandidates.at((*bestCC)), *bounds.second);
            return true;
          } else {
            // no split, we can simply apply the contraction to the current state
#ifdef PDW_MODULE_DEBUG_1
            std::cout << "Contract with " << *(contractionCandidates.at((*bestCC))) << ", results in bounds: " << bounds.first << std::endl;
#endif
            mCurrentState.applyContraction(contractionCandidates.at((*bestCC)), bounds.first);
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
              std::cout << "No model found, gain too small -> split!" << std::endl;
#endif
              //First extract the best variable for splitting
              carl::Variable splittingVar = mCurrentState.getBestSplitVariable();
              IntervalT oldInterval = mCurrentState.getBounds().getDoubleInterval(splittingVar);

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
    mLeftChild  = make_unique<ICPTree<Settings>>(this, mCurrentState.getBounds(), mOriginalVariables, mActiveSimpleBounds,mModule);
    mRightChild = make_unique<ICPTree<Settings>>(this, mCurrentState.getBounds(), mOriginalVariables, mActiveSimpleBounds,mModule);
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
  void ICPTree<Settings>::generateConflictReasons() {
    // we start with only the conflicting variable
    // and determine all involved constraints and variables
    accumulateInvolvedConstraintsAndVariables(mConflictingVariables, mConflictingConstraints,
      mCurrentState.getAppliedContractionCandidates(), (int) (mCurrentState.getAppliedContractionCandidates().size()) - 1, -1);

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
  bool ICPTree<Settings>::addConstraint(const ConstraintT& _constraint, const ConstraintT& _origin ) {
    // we add all constraints to the variable bounds, always
    // even though the variable bounds cannot deduce anything from non-simple bounds
    // it will still need to know about the occurring variables
    mCurrentState.getBounds().addBound(_constraint, _origin);

    // however, in order to propagate and later remove simple bounds
    // we need to store them seperately
    if (ICPUtil<Settings>::isSimpleBound(_constraint)) {
      mActiveSimpleBounds.insert(_constraint);
    }

    // we need to clear the unsat results of the previous search
    clearUnsat();

    // we need to add the constraint to all children as well
    // otherwise the leaf nodes will not know about the new constraint
    bool isLeftConflicting = false;
    if (mLeftChild) {
      isLeftConflicting = !mLeftChild->addConstraint(_constraint, _origin);
    }

    bool isRightConflicting = false;
    if (mRightChild) {
      isRightConflicting = !mRightChild->addConstraint(_constraint, _origin);
    }

    if (isLeftConflicting && isRightConflicting) {
      accumulateConflictReasons();
      return false;
    }
    else if (mCurrentState.getBounds().isConflicting()) {
      // the added constraint yields in an unsat search tree
      // directly for this current node
      handleUnsat();
      return false;
    }
    else {
      return true;
    }
  }

  template<class Settings>
  void ICPTree<Settings>::removeConstraint(const ConstraintT& _constraint, const ConstraintT& _origin ) {
    // since we always add every constraint, we also need to remove every one
    mCurrentState.getBounds().removeBound(_constraint, _origin);

    // also remove simple bounds from the active simple bound set
    if (ICPUtil<Settings>::isSimpleBound(_constraint)) {
      mActiveSimpleBounds.erase(_constraint);
    }

    clearUnsat();

    // actually remove the constraint from the current icp state
    // this method will revert all applied contraction candidates
    bool isUsed = mCurrentState.removeConstraint(_constraint);

    // if the constraint that should be removed has not been used at all
    // we can simply tell the children to remove the constraint and be done with it
    bool isLeftUnsat = false;
    bool isRightUnsat = false;
    if (!isUsed) {
      if (mLeftChild) {
        mLeftChild->removeConstraint(_constraint, _origin);
        isLeftUnsat = mLeftChild->isUnsat();
      }

      if (mRightChild) {
        mRightChild->removeConstraint(_constraint, _origin);
        isRightUnsat = mRightChild->isUnsat();
      }
    }
    // it has been used, so after the icp state reverted all applied contractions
    // we need to remove the children
    else {
      mLeftChild.reset();
      mRightChild.reset();
      mSplitDimension = std::experimental::nullopt;
    }

    // removal of this bound might have made this state sat again
    if (isLeftUnsat && isRightUnsat) {
      accumulateConflictReasons();
    }
    else if (mCurrentState.getBounds().isConflicting()) {
      // reconstruct the unsat set
      handleUnsat();
    }
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

  /**
   * Given an initial set of variables and constraints, this function determines
   * all other involved variables and constraints from the given contraction candidate iterator.
   *
   * I.e., this method will traverse the given iterator from begin to end, and check
   * whether any involved variables occur in the constraint of the current contraction candidate,
   * or if the constraint itself is an involved constraint.
   * If this is the case, all the variables from that constraint will be added to involvedVars
   * and the constraint itself to involvedConstraints.
   *
   * @param involvedVars a set of initial involved vars. will be updated during this method
   * @param involvedConstraints a set of initial involved constraints. will be updated during this method
   * @param candidates a list of contraction candidates that should be used to determine involvement
   * @param startIndex where to start the search for involved constraints
   *                   if startIndex > endIndex, the list will be traversed in reverse order
   * @param endIndex where to end the search for involved constraints (this index will not be checked)
   *                   if startIndex > endIndex, the list will be traversed in reverse order
   */

  template<class Settings>
  void ICPTree<Settings>::accumulateInvolvedConstraintsAndVariables(std::set<carl::Variable>& involvedVars,
                                                 std::set<ConstraintT>&    involvedConstraints,
                                                 vector<ICPContractionCandidate*>& candidates,
                                                 int startIndex, int endIndex) {
    //cout << "Initial involved vars: " << involvedVars << endl;
    //cout << "Initial involved constraints: " << involvedConstraints << endl;

    int step = (startIndex <= endIndex) ? 1 : -1;

    for (int i = startIndex; i != endIndex; i += step) {
      ICPContractionCandidate* it = candidates[i];
      //cout << "Check [" << i << "] if " << *it << " is involved...";
      if (involvedConstraints.count(it->getConstraint()) > 0 ||
          ICPUtil<Settings>::occurVariablesInConstraint(involvedVars, it->getConstraint())) {
        // the constraint itself is an involved constraint
        // or it contains an involved variable
        //cout << " yep!" << endl;
        auto cVars = it->getConstraint().variables();

        //cout << "Adding " << cVars << " to involved vars." << endl;
        involvedVars.insert(cVars.begin(), cVars.end());
        //cout << "Adding " << it->getConstraint() << " to involved constraints." << endl;
        involvedConstraints.insert(it->getConstraint());
      }
      else {
        //cout << " nope." << endl;
      }
    }
    //cout << "Final involved vars: " << involvedVars << endl;
    //cout << "Final involved constraints: " << involvedConstraints << endl;
  }
}
