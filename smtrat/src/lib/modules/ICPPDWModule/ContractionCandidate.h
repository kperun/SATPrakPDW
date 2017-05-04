/*
 * File:   ContractionCandidate.h
 * Author: David
 */

#pragma once

#include "../../Common.h"

namespace smtrat
{
    class ContractionCandidate
    {
        private:
            carl::Variable* mVariable;
            const ConstraintT* mConstraint;

        public:
            ContractionCandidate(carl::Variable* var, const ConstraintT* constraint):
                mVariable(var),
                mConstraint(constraint)
            {
            }

            ~ContractionCandidate() {
            }

            carl::Variable* getVariable();
            void setVariable(carl::Variable* var);
            const ConstraintT* getConstraint();
            void setConstraint(const ConstraintT* constraint);
    };
}
