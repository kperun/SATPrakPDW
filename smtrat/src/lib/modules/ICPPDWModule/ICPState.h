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

    /**
     * Represents a state of the ICP algorithm.
     *
     * A state stores all the contraction candidates that have been applied.
     * The current search box is stored in ICPPDWModule.
     * In case of a split, the state stores the dimension (i.e. variable) in which the split occurred.
     * In case of unsatisfiability, this state stores the reasons (i.e. constraints).
     */
    class ICPState
    {
        private:
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
