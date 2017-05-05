/*
 * File:   ContractionCandidate.h
 * Author: David
 */

#pragma once

#include "../../Common.h"

namespace smtrat
{
    /**
     * This class represents a contraction candidate (x, c) where x is a variable
     * and c is a constraint.
     */
    class ICPContractionCandidate
    {
        private:
            carl::Variable mVariable;
            ConstraintT mConstraint;

        public:
            ICPContractionCandidate(carl::Variable& var, const ConstraintT& constraint):
                mVariable(var),
                mConstraint(constraint)
            {
            }

            ~ICPContractionCandidate() {
            }

            carl::Variable& getVariable();
            void setVariable(carl::Variable& var);
            ConstraintT& getConstraint();
            void setConstraint(const ConstraintT& constraint);
    };
}
