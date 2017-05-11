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
     * A state stores the current search box.
     * It stores all the contraction candidates that have been applied.
     * It also stores all the constraints that were added as a result of contraction (lower & upper bounds).
     * In case of a split, the state stores the dimension (i.e. variable) in which the split occurred.
     * In case of unsatisfiability, this state stores the reasons (i.e. constraints).
     */
    class ICPState
    {
        private:
            // the current search box
            vb::VariableBounds<FormulaT> mBounds;

            /* 
             * the contraction candidates that have been applied
             * they will be stored in the order they have been applied
             */
            vector<ICPContractionCandidate*> mContractionCandidates;

            /* 
             * after we apply a contraction candidate, we add the lower and upper
             * bounds of the contracted interval as constraints. those constraints
             * are stored in this vector.
             * the index of constraint pairs for a contracted interval coincides with
             * the index of its contraction candidate in mContractionCandidates.
             */
            vector<std::pair<ConstraintT, ConstraintT>> mAppliedIntervalConstraints;

            // dimension in which the split occurred
            // TODO optional<carl::Variable>
            carl::Variable mSplitDimension;

            // conflicting clauses
            std::set<ConstraintT> mConflictingConstraints;

        public:
            ICPState();
            ~ICPState();

            /**
             * Returns the current search box as a map from variables to intervals.

             * @return reference to the search box
             */
            vb::VariableBounds<FormulaT>& getBounds();

            /**
             * Sets or updates the current interval bound for a specific variable.
             * Internally it adds two new constraints for the lower and upper bounds.

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

            vector<std::pair<ConstraintT, ConstraintT>>& getAppliedIntervalConstraints();
            void addAppliedIntervalConstraints(const ConstraintT& lowerBound, const ConstraintT& upperBound);

            carl::Variable getSplitDimension();
            void setSplitDimension(carl::Variable var);

            std::set<ConstraintT>& getConflictingConstraints();
            void addConflictingConstraint(const ConstraintT& constraint);
    };
}
