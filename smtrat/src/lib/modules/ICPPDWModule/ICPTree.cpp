#include "ICPTree.h"
#include "ICPUtil.h"
#include "ICPPDWModule.h"

namespace smtrat
{

  template class ICPTree<ICPPDWSettings1>;

  template<class Settings>
  ICPTree<Settings>::ICPTree() :
    mCurrentState(this),
    mParentTree(),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mOriginalVariables(),
    mIsUnsat(false),
    mActiveSimpleBounds()
  {
  }

  template<class Settings>
  ICPTree<Settings>::ICPTree(std::set<carl::Variable>* originalVariables) :
    mCurrentState(originalVariables,this),
    mParentTree(),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mOriginalVariables(originalVariables),
    mIsUnsat(false),
    mActiveSimpleBounds()
  {
  }

  template<class Settings>
  ICPTree<Settings>::ICPTree(ICPTree<Settings>* parent, const vb::VariableBounds<ConstraintT>& parentBounds,std::set<carl::Variable>* originalVariables, const std::set<ConstraintT>& simpleBounds) :
    mCurrentState(parentBounds,originalVariables,this),
    mParentTree(parent),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mOriginalVariables(originalVariables),
    mIsUnsat(false),
    mActiveSimpleBounds(simpleBounds)
  {
    // we need to actually add all the simple bounds to our new icp state
    for (const ConstraintT& simpleBound : mActiveSimpleBounds) {
      mCurrentState.getBounds().addBound(simpleBound, simpleBound);
    }
  }


  template<class Settings>
  void ICPTree<Settings>::printVariableBounds() {
    SMTRAT_LOG_INFO("smtrat.module","Variable bounds:");
    for (const auto& mapEntry : mCurrentState.getBounds().getIntervalMap()) {
      SMTRAT_LOG_INFO("smtrat.module",mapEntry.first << " in " << mapEntry.second);
    }
    SMTRAT_LOG_INFO("smtrat.module",std::endl);
  }

  template<class Settings>
  bool ICPTree<Settings>::contract(vector<ICPContractionCandidate*>& contractionCandidates,ICPPDWModule<Settings>* module) {
    while(true) {
      printVariableBounds();

      // first we need to make sure the bounds are still satisfiable
      // i.e. no variable has an empty interval
      if (mCurrentState.getBounds().isConflicting()) {
        // if the bounds do contain a conflict, this ICP node is unsatisfiable
        mIsUnsat = true;

        // so we retrieve the set of conflicting constraints and add them to our state
        carl::Variable conflictVar = mCurrentState.getConflictingVariable();
        mConflictingConstraints = getConflictReasons(conflictVar);

        SMTRAT_LOG_INFO("smtrat.module","Bounds are conflicting!" << std::endl
            << "Reasons: ");
        for (const ConstraintT& c : mConflictingConstraints) {
          SMTRAT_LOG_INFO("smtrat.module",c << ", ");
        }
        SMTRAT_LOG_INFO("smtrat.module",std::endl);

        // we have determined that this ICP search tree is unsatisfiable
        // if this tree was the last child of the parent, then this could mean that
        // every child of the parent is unsat, and thus, the parent is unsat
        // if that is the case, we need to propagate and accumulate the conflicting reasons
        if (mParentTree) {
          (*mParentTree)->accumulateConflictReasons(conflictVar);
        }

        // we will terminate, but we did not split the search space
        return false;
      }
      // if we met some other termination condition (e.g. target diameter reached
      else if (mCurrentState.isTerminationConditionReached()) {
        SMTRAT_LOG_INFO("smtrat.module","Termination condition reached." << std::endl);

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
            SMTRAT_LOG_INFO("smtrat.module","Split on " << contractionCandidates.at((*bestCC))->getVariable() << " by " << bounds.first << " vs " << (*bounds.second) << endl);
            split(contractionCandidates.at((*bestCC))->getVariable());

            // we splitted the tree, now we need to apply the intervals for the children
            mLeftChild->getCurrentState().applyContraction(contractionCandidates.at((*bestCC)),  bounds.first );
            mRightChild->getCurrentState().applyContraction(contractionCandidates.at((*bestCC)), *bounds.second);
            return true;
          } else {
            // no split, we can simply apply the contraction to the current state
            SMTRAT_LOG_INFO("smtrat.module","Contract with " << *(contractionCandidates.at((*bestCC))) << ", results in bounds: " << bounds.first << std::endl);
            mCurrentState.applyContraction(contractionCandidates.at((*bestCC)), bounds.first);
          }
        }else{ //otherwise perform a split
          SMTRAT_LOG_INFO("smtrat.module","Start guessing model before split!\n");
          std::experimental::optional<Model> model= (*module).getSolution(this);
          //if we found a model, just terminate with false indicating that no split occurred
            if(model){
              SMTRAT_LOG_INFO("smtrat.module","Model guessed without split!\n");
              (*module).setModel((*model));
              mIsUnsat = false;
              return false;
            }
            else {
              //now it is not sat, thus we have to split further
              SMTRAT_LOG_INFO("smtrat.module","No model found, gain too small -> split!\n");
              //First extract the best variable for splitting
              carl::Variable splittingVar = mCurrentState.getBestSplitVariable();
              IntervalT oldInterval = mCurrentState.getBounds().getDoubleInterval(splittingVar);
              
              std::pair<IntervalT, IntervalT> newIntervals = ICPUtil<Settings>::splitInterval(oldInterval);

              SMTRAT_LOG_INFO("smtrat.module", "Split on " << splittingVar << " with new intervals: "
                  << newIntervals.first << " and " << newIntervals.second << endl);

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
  bool ICPTree<Settings>::isUnsat() {
    return mIsUnsat;
  }


  template<class Settings>
  void ICPTree<Settings>::split(carl::Variable var) {
    mSplitDimension = var;

    // we create two new search trees with copies of the original bounds
    mLeftChild  = make_unique<ICPTree<Settings>>(this, mCurrentState.getBounds(), mOriginalVariables, mActiveSimpleBounds);
    mRightChild = make_unique<ICPTree<Settings>>(this, mCurrentState.getBounds(), mOriginalVariables, mActiveSimpleBounds);
  }

  template<class Settings>
  std::set<ConstraintT> ICPTree<Settings>::getConflictReasons(carl::Variable conflictVar) {
    std::set<ConstraintT> conflictReasons;

    // retrieve all constraints that have been used
    // TODO: only use constraints that have been used to contract the conflict variable (in the current ICP state)
    vector<ICPContractionCandidate*> appliedCCs = mCurrentState.getAppliedContractionCandidates();
    for (ICPContractionCandidate* cc : appliedCCs) {
      conflictReasons.insert(cc->getConstraint());
    }

    // and we need to add all used simple bounds
    // we need to do this manually here, because the search tree never "contracts" with simple bounds
    // and thus, they will not appear in its conflicting constraint set
    for (const ConstraintT& c : mActiveSimpleBounds) {
      // we actually only need to add those simple bounds where the variable was used
      // during one of the contraction steps
      if (ICPUtil<Settings>::occursVariableInConstraints(*(c.variables().begin()), conflictReasons)) {
        conflictReasons.insert(c);
      }
    }

    return conflictReasons;
  }

  template<class Settings>
  void ICPTree<Settings>::accumulateConflictReasons(carl::Variable conflictVar) {
    if (mLeftChild && mLeftChild->isUnsat() && mRightChild && mRightChild->isUnsat()) {
      mIsUnsat = true;
      std::set<ConstraintT> leftReasons = mLeftChild->getConflictingConstraints();
      std::set<ConstraintT> rightReasons = mRightChild->getConflictingConstraints();
      mConflictingConstraints.insert(leftReasons.begin(), leftReasons.end());
      mConflictingConstraints.insert(rightReasons.begin(), rightReasons.end());

      // we accumulated the conflict reasons of the left and right child
      // and now we need to add the conflict reasons of this parent tree
      std::set<ConstraintT> parentReasons = getConflictReasons(conflictVar);
      mConflictingConstraints.insert(parentReasons.begin(), parentReasons.end());

      // we need to accumulate further
      if (mParentTree) {
        (*mParentTree)->accumulateConflictReasons(conflictVar);
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

    if ((isLeftConflicting && isRightConflicting) || mCurrentState.getBounds().isConflicting()) {
      // the added constraint yields in an unsat search tree
      mIsUnsat = true;
      // TODO: what do with mConflictingConstraints?
      return false;
    }
    else {
      // TODO: what do with mConflictingConstraints?
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
    }

    // removal of this bound might have made this state sat again
    if ((isLeftUnsat && isRightUnsat) || mCurrentState.getBounds().isConflicting()) {
      mIsUnsat = true;
      // TODO: what do with mConflictingConstraints?
    }
    else {
      mIsUnsat = false;
      mConflictingConstraints.clear();
    }
  }
}
