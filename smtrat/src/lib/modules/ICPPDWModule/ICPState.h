/*
 * File:   ICPState.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "ICPContractionCandidate.h"

namespace smtrat
{
    typedef RationalInterval IntervalT;
    typedef std::map<carl::Variable, IntervalT> BoxT;

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
            BoxT mSearchBox;

            // the contraction candidate that has been applied
            ICPContractionCandidate* mContractionCandidate;
            
            // dimension in which the split occurred
            carl::Variable* mSplitDimension;

            // conflicting clauses
            vector<ConstraintT*> mConflictingConstraints;

        public:
            ICPState();
            ICPState(ICPContractionCandidate* contractionCandidate);
            ~ICPState();

            BoxT* getBox();
            void setInterval(const carl::Variable& var, const RationalInterval& interval);
            ICPContractionCandidate* getContractionCandidate();
            void setContractionCandidate(ICPContractionCandidate* contractionCandidate);
            carl::Variable* getSplitDimension();
            void setSplitDimension(carl::Variable* var);
            vector<ConstraintT*>* getConflictingConstraints();
            void addConflictingConstraint(ConstraintT* constraint);
    };
}
