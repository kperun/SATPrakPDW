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
            ICPContractionCandidate();
            ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint);
            ~ICPContractionCandidate();

            carl::Variable getVariable();
            void setVariable(const carl::Variable& var);

            ConstraintT& getConstraint();
            void setConstraint(const ConstraintT& constraint);

            friend inline std::ostream& operator <<(std::ostream& os, const ICPContractionCandidate& cc) {
                os << "(" << cc.mVariable << ", " << cc.mConstraint << ")";
                return os;
            }
    };
}
