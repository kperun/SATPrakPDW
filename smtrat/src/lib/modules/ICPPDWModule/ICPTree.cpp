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
