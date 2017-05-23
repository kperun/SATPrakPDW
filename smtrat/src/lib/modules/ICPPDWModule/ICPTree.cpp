#include "ICPTree.h"
#include "ICPUtil.h"

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
    mIsUnsat(false)
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
    mIsUnsat(false)
  {
  }

  template<class Settings>
  ICPTree<Settings>::ICPTree(ICPTree<Settings>* parent, const vb::VariableBounds<ConstraintT>& parentBounds,std::set<carl::Variable>* originalVariables) :
    mCurrentState(parentBounds,originalVariables,this),
    mParentTree(parent),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mIsUnsat(false)
  {
    mOriginalVariables = originalVariables;
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
  bool ICPTree<Settings>::contract(vector<ICPContractionCandidate*>& contractionCandidates) {
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
          (*mParentTree)->accumulateConflictReasons();
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
        }else{ //otherwise terminate and return false
          SMTRAT_LOG_INFO("smtrat.module","Gain too small -> split!\n");
          //First extract the best variable for splitting
          carl::Variable splittingVar = mCurrentState.getBestSplitVariable();
          IntervalT oldInterval = mCurrentState.getBounds().getDoubleInterval(splittingVar);
          
          std::pair<IntervalT, IntervalT> newIntervals = ICPUtil::splitInterval(oldInterval);

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
    mLeftChild  = make_unique<ICPTree<Settings>>(this, mCurrentState.getBounds(), mOriginalVariables);
    mRightChild = make_unique<ICPTree<Settings>>(this, mCurrentState.getBounds(), mOriginalVariables);
  }

  template<class Settings>
  std::set<ConstraintT> ICPTree<Settings>::getConflictReasons(carl::Variable conflictVar) {
    std::set<ConstraintT> conflictReasons;

    // retrieve all constraints that have been used to contract this variable (in the current ICP state)
    vector<ICPContractionCandidate*> appliedCCs = mCurrentState.getAppliedContractionCandidates();
    for (ICPContractionCandidate* cc : appliedCCs) {
      conflictReasons.insert(cc->getConstraint());
    }

    // retrieve all constraints that have been used to contract this variable (in all parent states)
    if(mParentTree) {
      std::set<ConstraintT> parentReasons = (*mParentTree)->getConflictReasons(conflictVar);
      conflictReasons.insert(parentReasons.begin(), parentReasons.end());
    }

    return conflictReasons;
  }

  template<class Settings>
  void ICPTree<Settings>::accumulateConflictReasons() {
    if (mLeftChild && mLeftChild->isUnsat() && mRightChild && mRightChild->isUnsat()) {
      mIsUnsat = true;
      mConflictingConstraints.insert(mLeftChild->getConflictingConstraints().begin(),
                                     mLeftChild->getConflictingConstraints().end());
      mConflictingConstraints.insert(mRightChild->getConflictingConstraints().begin(),
                                     mRightChild->getConflictingConstraints().end());
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
    mCurrentState.getBounds().addBound(_constraint, _origin);
    
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
    mCurrentState.getBounds().removeBound(_constraint, _origin);

    // TODO:
    /*
     * Go through the contraction candidate list from first to last applied cc.
     * If a cc with the removed constraint was applied, we need to revert all following applied CCs.
     * This can be done in the following steps:
     * 1. delete the children (if there are any)
     * 2. go through the appliedIntervalBounds from last to the current cc
     *    and remove those bounds form the variable bounds object
     */

    // we need to recursively remove the bounds form child trees as well
    bool isLeftConflicting = false;
    if (mLeftChild) {
      mLeftChild->removeConstraint(_constraint, _origin);
      isLeftConflicting = mLeftChild->isUnsat();
    }

    bool isRightConflicting = false;
    if (mRightChild) {
      mRightChild->removeConstraint(_constraint, _origin);
      isRightConflicting = mRightChild->isUnsat();
    }

    // removal of this bound might have made this state sat again
    if ((isLeftConflicting && isRightConflicting) || mCurrentState.getBounds().isConflicting()) {
      mIsUnsat = true;
      // TODO: what do with mConflictingConstraints?
    }
    else {
      mIsUnsat = false;
      mConflictingConstraints.clear();
    }
  }
}
