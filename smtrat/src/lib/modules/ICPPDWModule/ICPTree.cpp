#include "ICPTree.h"

namespace smtrat
{

  ICPTree::ICPTree() :
    mCurrentState(this),
    mParentTree(),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mOriginalVariables()
  {
  }

  ICPTree::ICPTree(std::set<carl::Variable>* originalVariables) :
    mCurrentState(originalVariables,this),
    mParentTree(),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints(),
    mOriginalVariables(originalVariables)
  {
  }

  ICPTree::ICPTree(ICPTree* parent, const vb::VariableBounds<ConstraintT>& parentBounds,std::set<carl::Variable>* originalVariables) :
    mCurrentState(parentBounds,originalVariables,this),
    mParentTree(parent),
    mLeftChild(),
    mRightChild(),
    mSplitDimension(),
    mConflictingConstraints()
  {
    mOriginalVariables = originalVariables;
  }

  void ICPTree::printVariableBounds() {
    SMTRAT_LOG_INFO("smtrat.module","Variable bounds:");
    for (const auto& mapEntry : mCurrentState.getBounds().getIntervalMap()) {
      SMTRAT_LOG_INFO("smtrat.module",mapEntry.first << " in " << mapEntry.second);
    }
    SMTRAT_LOG_INFO("smtrat.module",std::endl);
  }

  bool ICPTree::contract(vector<ICPContractionCandidate*>& contractionCandidates) {
    while(true) {
      printVariableBounds();

      // first we need to make sure the bounds are still satisfiable
      // i.e. no variable has an empty interval
      if (mCurrentState.getBounds().isConflicting()) {
        // if the bounds do contain a conflict, this ICP node is unsatisfiable
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
          carl::Variable splittingVar = mCurrentState.getBestSplitVariable(contractionCandidates);
          IntervalT oldInterval = mCurrentState.getBounds().getDoubleInterval(splittingVar);
          IntervalT firstNewInterval(oldInterval.lower(), oldInterval.lowerBoundType(), oldInterval.lower() + oldInterval.diameter() / 2.0, carl::BoundType::WEAK);
          IntervalT secondNewInterval(oldInterval.lower() + oldInterval.diameter() / 2.0, carl::BoundType::STRICT, oldInterval.upper(), oldInterval.upperBoundType());
          SMTRAT_LOG_INFO("smtrat.module", "Split on " << splittingVar << " with new intervals: "
              << firstNewInterval << " and " << secondNewInterval << endl);
          split(splittingVar);
          //TODO: Think about origins
          mLeftChild->getCurrentState().setInterval(splittingVar, firstNewInterval,mCurrentState.getBounds().getOriginsOfBounds(splittingVar)[0]);
          mRightChild->getCurrentState().setInterval(splittingVar, secondNewInterval,mCurrentState.getBounds().getOriginsOfBounds(splittingVar)[0]);
          return true;
        }
      }
    }
  }

  ICPState& ICPTree::getCurrentState() {
    return mCurrentState;
  }

  std::experimental::optional<ICPTree*> ICPTree::getParentTree() {
    return mParentTree;
  }

  ICPTree* ICPTree::getLeftChild() {
    return mLeftChild.get();
  }

  ICPTree* ICPTree::getRightChild() {
    return mRightChild.get();
  }

  bool ICPTree::isLeaf() {
    return (!mLeftChild && !mRightChild);
  }

  vector<ICPTree*> ICPTree::getLeafNodes() {
    vector<ICPTree*> leafNodes;
    if (isLeaf()) {
      leafNodes.push_back(this);
    }
    else {
      if (mLeftChild) {
        vector<ICPTree*> leftLeafNodes = mLeftChild->getLeafNodes();
        leafNodes.insert(leafNodes.end(), leftLeafNodes.begin(), leftLeafNodes.end());
      }
      if (mRightChild) {
        vector<ICPTree*> rightLeafNodes = mRightChild->getLeafNodes();
        leafNodes.insert(leafNodes.end(), rightLeafNodes.begin(), rightLeafNodes.end());
      }
    }

    return leafNodes;
  }

  std::experimental::optional<carl::Variable> ICPTree::getSplitDimension() {
    return mSplitDimension;
  }

  std::set<ConstraintT>& ICPTree::getConflictingConstraints() {
    return mConflictingConstraints;
  }

  bool ICPTree::isUnsat() {
    return !mConflictingConstraints.empty();
  }

  void ICPTree::split(carl::Variable var) {
    mSplitDimension = var;

    // we create two new search trees with copies of the original bounds
    mLeftChild  = make_unique<ICPTree>(this, mCurrentState.getBounds(),mOriginalVariables);
    mRightChild = make_unique<ICPTree>(this, mCurrentState.getBounds(),mOriginalVariables);
  }

  std::set<ConstraintT> ICPTree::getConflictReasons(carl::Variable conflictVar) {
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

  void ICPTree::accumulateConflictReasons() {
    if (mLeftChild && mLeftChild->isUnsat() && mRightChild && mRightChild->isUnsat()) {
      mConflictingConstraints.insert(mLeftChild->getConflictingConstraints().begin(),
          mLeftChild->getConflictingConstraints().end());
      mConflictingConstraints.insert(mRightChild->getConflictingConstraints().begin(),
          mRightChild->getConflictingConstraints().end());
    }
  }

  int ICPTree::getNumberOfSplits(){
    return getRoot()->getNumberOfSplitsRecursive();
  }

  ICPTree* ICPTree::getRoot(){
    if(mParentTree) {
      return (*mParentTree)->getRoot();
    }
    return this;
  }

  int ICPTree::getNumberOfSplitsRecursive(){
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

}
