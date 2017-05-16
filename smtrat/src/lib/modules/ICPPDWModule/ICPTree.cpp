#include "ICPTree.h"

namespace smtrat
{

    ICPTree::ICPTree() :
        mCurrentState(),
        mParentTree(nullptr),
        mSplitDimension(),
        mLeftChild(),
        mRightChild()
    {
    }

    ICPTree::ICPTree(ICPTree* parent, const vb::VariableBounds<ConstraintT>& parentBounds) :
        mCurrentState(parentBounds),
        mParentTree(parent),
        mSplitDimension(),
        mLeftChild(),
        mRightChild()
    {
    }

    bool ICPTree::contract(vector<ICPContractionCandidate>& contractionCandidates) {
        while(true) {
            std::cout << "\nVariable bounds:" << std::endl;
            for (const auto& mapEntry : mCurrentState.getBounds().getIntervalMap()){
                std::cout << mapEntry.first << " in " << mapEntry.second << std::endl;
            }

            // first we need to make sure the bounds are still satisfiable
            // i.e. no variable has an empty interval
            if (mCurrentState.getBounds().isConflicting()) {
                // if the bounds do contain a conflict, this ICP node is unsatisfiable
                // so we retrieve the set of conflicting constraints and add them to our state
                // TODO: This method only returns the last constraint that was used
                //       so implement a method which actually determines the unsat core
                //       Idea: use mCurrentState.getBounds().getOriginsOfBounds(var) to find all 
                //             constraints which were involved in achieving the bounds for a variable
                mCurrentState.setConflictingConstraints(mCurrentState.getBounds().getConflict());

                std::cout << "Bounds are conflicting!" << std::endl;
                std::cout << "Reasons: " << std::endl;
                for (const ConstraintT& c : mCurrentState.getConflictingConstraints()) {
                    std::cout << c << ", ";
                }
                std::cout << std::endl;

                // TODO: propagate UNSAT if both child trees are unsat
                // or maybe do this in a seperate method

                // we will terminate, but we did not split the search space
                return false;
            }
            // if we met some other termination condition (e.g. target diameter reached
            else if (mCurrentState.isTerminationConditionReached()) {
                std::cout << "Termination condition reached." << std::endl;

                // we will terminate, but we did not split the search space
                return false;
            }
            // we can contract
            else {

                // We have to pick the best contraction candidate that we want to apply
                ICPContractionCandidate& bestCC = mCurrentState.getBestContractionCandidate(contractionCandidates);
                OneOrTwo<IntervalT> bounds = bestCC.getContractedInterval(mCurrentState.getBounds());

                if(bounds.second){
                    // We contracted to two intervals, so we need to split 
                    cout << "Split on " << bestCC.getVariable() << " by " << bounds.first << " vs " << (*bounds.second) << endl;
                    split(bestCC.getVariable());

                    // we splitted the tree, now we need to apply the intervals for the children
                    mLeftChild ->getCurrentState().applyContraction(&bestCC,  bounds.first );
                    mRightChild->getCurrentState().applyContraction(&bestCC, *bounds.second);

                    return true;
                } else {
                    // no split, we can simply apply the contraction to the current state
                    std::cout << "Contract with " << bestCC << ", results in bounds: " << bounds.first << std::endl;
                    mCurrentState.applyContraction(&bestCC, bounds.first);
                }
            }
        }
    }

    void ICPTree::split(carl::Variable var) {
        mSplitDimension = var;

        // we create two new search trees with copies of the original bounds
        mLeftChild  = make_unique<ICPTree>(this, mCurrentState.getBounds());
        mRightChild = make_unique<ICPTree>(this, mCurrentState.getBounds());
    }

    ICPState& ICPTree::getCurrentState() {
        return mCurrentState;
    }

    void ICPTree::setCurrentState(const ICPState& state) {
        mCurrentState = state;
    }

    ICPTree* ICPTree::getParentTree() {
        return mParentTree;
    }

    carl::Variable ICPTree::getSplitDimension() {
        return mSplitDimension;
    }

    void ICPTree::setSplitDimension(carl::Variable splitDimension) {
        mSplitDimension = splitDimension;
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
}
