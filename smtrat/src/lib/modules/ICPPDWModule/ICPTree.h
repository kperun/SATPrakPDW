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
            // TODO: optional<ICPTree*>
            ICPTree* mParentTree;

            // the child states
            vector<ICPTree> mChildTrees;

        public:
            ICPTree();
            ICPTree(ICPTree* parent);
            ~ICPTree();

            /**
             * Contracts the current ICP state until either:
             * 1) A split occurrs.
             *    In this case, two new child trees which correspond to the splitted search space
             *    will be added to mChildTrees, and true will be returned.
             * 2) The bounds are UNSAT.
             *    In this case, the current ICP state will contain a set of conflicting constraints,
             *    and - since no split occurred - false will be returned.
             * 3) Some other termination criterium was met.
             *    (E.g. the target diameter for all intervals was reached)
             *    In this case, no child trees will be added, and no conflicting constraints will
             *    be determined. Since no split occurred, false will be returned.
             *
             * A method caller can determine which of these cases happened through the return value
             * of this method and the isUnsat method of the current ICP state.
             * 
             * @param contractionCandidates A set of contraction candidates that can be applied
             * @return whether a split occurred
             */
            bool contract(vector<ICPContractionCandidate>& contractionCandidates);

            ICPState& getCurrentState();
            void setCurrentState(const ICPState& state);

            ICPTree* getParentTree();

            vector<ICPTree>& getChildTrees();
            void addChildTree(const ICPTree& child);
            bool isLeaf();
    };
}
