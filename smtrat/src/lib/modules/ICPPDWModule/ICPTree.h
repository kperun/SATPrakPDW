/*
 * File:   ICPTree.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "ICPState.h"

namespace smtrat
{
    /**
     * Represents the ICP search tree.
     */
    class ICPTree
    {
        private:
            // the current ICP state.
            ICPState mCurrentState;

            // the parent ICP state
            ICPTree* mParentTree;

            // the child states
            vector<ICPTree> mChildTrees;

        public:
            ICPTree();
            ~ICPTree();

            ICPState& getCurrentState();
            void setCurrentState(const ICPState& state);

            ICPTree* getParentTree();
            vector<ICPTree>& getChildTrees();
            void addChildTree(const ICPTree& child);
            bool isLeaf();
    };
}
