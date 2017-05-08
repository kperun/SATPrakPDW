#include "ICPTree.h"

namespace smtrat
{

    ICPTree::ICPTree() :
        mCurrentState(nullptr),
        mParentTree(nullptr)
    {
    }

    ICPTree::ICPTree(ICPState* state, ICPTree* parent) :
        mCurrentState(state),
        mParentTree(parent)
    {
    }

    ICPTree::~ICPTree() {

    }

    ICPState* ICPTree::getCurrentState() {
        return mCurrentState;
    }

    void ICPTree::setCurrentState(ICPState* state) {
        mCurrentState = state;
    }

    ICPTree* ICPTree::getParentTree() {
        return mParentTree;
    }

    vector<ICPTree*>* ICPTree::getChildTrees() {
        return &mChildTrees;
    }

    void ICPTree::addChildTree(ICPTree* child) {
        mChildTrees.push_back(child);
    }

    bool ICPTree::isLeaf() {
        return mChildTrees.empty();
    }
}