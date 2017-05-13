#include "ICPTree.h"

namespace smtrat
{

    ICPTree::ICPTree() :
        mCurrentState(),
        mParentTree(nullptr),
        mChildTrees()
    {
    }

    ICPTree::ICPTree(ICPTree* parent) :
        mCurrentState(),
        mParentTree(parent),
        mChildTrees()
    {
    }

    ICPTree::~ICPTree() {
    }

    bool ICPTree::contract(vector<ICPContractionCandidate>& contractionCandidates) {
        // TODO

        // for now: hard-coded 10 iterations
        for (int i = 0; i < 10; i++) {
            std::cout << "\nICP Iteration #" << i << std::endl;
            std::cout << "\nContractions: " << std::endl;
            for (auto& cc : contractionCandidates) {
                std::pair<IntervalT, IntervalT> bounds = cc.getContractedInterval(mCurrentState.getBounds());
                std::cout << cc << " results in bound: " << bounds << std::endl;

                // this is incorrect. just for debugging, we always only choose the first interval (no splits)
                mCurrentState.setInterval(cc.getVariable(), bounds.first);
            }
            std::cout << "\nVariable bounds:" << std::endl;
            for (const auto& mapEntry : mCurrentState.getBounds().getIntervalMap()){
                std::cout << mapEntry.first << " in " << mapEntry.second << std::endl;
            }
        }

        return false;
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

    vector<ICPTree>& ICPTree::getChildTrees() {
        return mChildTrees;
    }

    void ICPTree::addChildTree(const ICPTree& child) {
        mChildTrees.push_back(child);
    }

    bool ICPTree::isLeaf() {
        return mChildTrees.empty();
    }
}
