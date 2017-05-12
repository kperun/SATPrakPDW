/*
 * File:   ICPState.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "ICPContractionCandidate.h"
#include "ICPPDWSettings.h"

namespace smtrat
{
    /**
     * Represents a state of the ICP algorithm.
     *
     * A state stores the current search box,
     * all the contraction candidates that have been applied, and
     * all the constraints that were added as a result of contraction (lower & upper bounds).
     * In case of a split, the state stores the dimension (i.e. variable) in which the split occurred.
     * In case of unsatisfiability, this state stores the reasons (i.e. constraints).
     */
    class ICPState
    {
        private:
            /**
             * The current search box.
             * VariableBounds internally stores a map from variables to intervals.
             * It also keeps track of which constraints were the reasons for the 
             * intervals. This way, we can automatically revert applied constraints.
             */
            vb::VariableBounds<FormulaT> mBounds;

            /**
             * The contraction candidates that have been applied.
             * They will be stored in the order that they have been applied.
             */
            vector<ICPContractionCandidate*> mAppliedContractionCandidates;

            /**
             * After we apply a contraction candidate, we add the lower and upper
             * bounds of the contracted interval as constraints. Those constraints
             * are stored in this vector.
             * The index of constraint pairs for a contracted interval coincides with
             * the index of its contraction candidate in mContractionCandidates.
             */
            vector<std::pair<ConstraintT, ConstraintT>> mAppliedIntervalConstraints;

            // dimension in which the split occurred, if a split occured
            // TODO optional<carl::Variable>
            carl::Variable mSplitDimension;

            /**
             * In case of UNSAT, this set will contain the reason for unsatisifiabilty.
             */
            std::set<ConstraintT> mConflictingConstraints;

        public:
            ICPState();
            ~ICPState();

            /**
             * Returns the current search box as VariableBounds.
             *
             * @return reference to the search box
             */
            vb::VariableBounds<FormulaT>& getBounds();

            /**
             * Updates the current interval bound for a specific variable.
             * Internally it adds two new constraints for the lower and upper bound.
             *
             * @param var The variable of which the interval should be updated
             * @param interval The new interval for that variable
             */
            void setInterval(carl::Variable var, const IntervalT& interval);

            /**
             * Returns the current interval bound for a specific variable.
             *
             * @param var The variable
             * @return The interval
             */
            IntervalT getInterval(carl::Variable var);

            vector<ICPContractionCandidate*>& getAppliedContractionCandidates();
            void addAppliedContractionCandidate(ICPContractionCandidate* contractionCandidate);

            vector<std::pair<ConstraintT, ConstraintT>>& getAppliedIntervalConstraints();
            void addAppliedIntervalConstraint(const ConstraintT& lowerBound, const ConstraintT& upperBound);

            carl::Variable getSplitDimension();
            void setSplitDimension(carl::Variable var);

            std::set<ConstraintT>& getConflictingConstraints();
            void addConflictingConstraint(const ConstraintT& constraint);
    };
}
