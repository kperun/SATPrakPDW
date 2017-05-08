/*
 * File:   ICPState.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "ICPContractionCandidate.h"

namespace smtrat
{
    typedef DoubleInterval IntervalT;
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
            ICPContractionCandidate mContractionCandidate;
            
            // dimension in which the split occurred
            carl::Variable mSplitDimension;

            // conflicting clauses
            vector<ConstraintT> mConflictingConstraints;

        public:
            ICPState();
            ~ICPState();

            /**
             * Returns the full search box, i.e. a map from variables to intervals.
             * @return a pointer to the map
             */
            BoxT& getBox();

            /**
             * Sets or updates the current interval bound for a specific variable.
             * @param var The variable of which the interval should be updated
             * @param interval The new interval for that variable
             */
            void setInterval(carl::Variable var, const IntervalT& interval);

            /**
             * Returns the current interval bound for a specific variable.
             * @param var The variable
             * @return The interval
             */
            IntervalT& getInterval(carl::Variable var);

            ICPContractionCandidate& getContractionCandidate();
            void setContractionCandidate(const ICPContractionCandidate& contractionCandidate);

            carl::Variable getSplitDimension();
            void setSplitDimension(carl::Variable var);

            vector<ConstraintT>& getConflictingConstraints();
            void addConflictingConstraint(const ConstraintT& constraint);
    };
}
