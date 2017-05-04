/*
 * File:   ICPState.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "ContractionCandidate.h"

namespace smtrat
{
    /**
     * Represents a state of the ICP algorithm.
     * A state contains the current search box and the contraction candidate that has been applied.
     * In case of a split, the state stores the dimension (i.e. variable) in which the split occurred.
     * In case of unsatisfiability, the state stores the reasons (i.e. constraints).
     */
    class ICPState
    {
        private:
            // the search box maps from variables to their current intervals
            std::map<carl::Variable*, RationalInterval> mSearchBox;
            ContractionCandidate* mContractionCandidate;
            
            // dimension in which the split occurred
            carl::Variable* mSplitDimension;
            // conflicting clauses
            vector<ConstraintT*> mConflictingConstraints;

        public:
            ICPState();
            ICPState(ContractionCandidate* contractionCandidate);
            ~ICPState();

            std::map<carl::Variable*, RationalInterval>* getBox();
            ContractionCandidate* getContractionCandidate();
            void setContractionCandidate(ContractionCandidate* contractionCandidate);
            carl::Variable* getSplitDimension();
            void setSplitDimension(carl::Variable* var);
            vector<ConstraintT*>* getConflictingConstraints();
            void addConflictingConstraint(ConstraintT* constraint);
    };
}
