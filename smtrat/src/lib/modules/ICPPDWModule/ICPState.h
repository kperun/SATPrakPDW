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
     *
     * A state contains the current search box and all the contraction candidates that have been applied.
     * In case of a split, the state stores the dimension (i.e. variable) in which the split occurred.
     * In case of unsatisfiability, this state stores the reasons (i.e. constraints).
     */
    class ICPState
    {
        private:
            // the search box maps from variables to their current intervals
            BoxT mSearchBox;

            // the contraction candidates that have been applied
            // they will be stored in the order they have been applied
            vector<ICPContractionCandidate*> mContractionCandidates;

            // dimension in which the split occurred
            carl::Variable mSplitDimension;

            // conflicting clauses
            std::set<ConstraintT> mConflictingConstraints;

        public:
            ICPState();
            ~ICPState();

            /**
             * Returns the full search box, i.e. a map from variables to intervals.
             * @return the map
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

            vector<ICPContractionCandidate*>& getContractionCandidates();
            void addContractionCandidate(ICPContractionCandidate* contractionCandidate);

            carl::Variable getSplitDimension();
            void setSplitDimension(carl::Variable var);

            std::set<ConstraintT>& getConflictingConstraints();
            void addConflictingConstraint(const ConstraintT& constraint);
    };
}
