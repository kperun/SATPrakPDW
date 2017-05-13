/*
 * File:   ContractionCandidate.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "../../datastructures/VariableBounds.h"
#include "carl/interval/Contraction.h"

namespace smtrat
{
    typedef DoubleInterval IntervalT;

    /**
     * This class represents a contraction candidate (x, c) 
     * where x is a variable and c is a constraint.
     */
    class ICPContractionCandidate
    {
        private:
            carl::Variable mVariable;
            ConstraintT mConstraint;
            
            // this contractor helps us with applying the contraction of this candidate
            Contractor<carl::SimpleNewton> mContractor;

        public:
            ICPContractionCandidate(const ICPContractionCandidate& rhs);
            ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint);
            ~ICPContractionCandidate();

            /**
             * Calculates the contracted interval of this contraction candidate.
             * I.e., it will solve the constraint for mVariable and insert the given variable bounds.
             * The result may be either one or two intervals, depending on the order of the variable.
             * 
             * @param _bounds The variable bounds
             * @return a pair of resulting intervals
             *         in case the result is only one interval, the second element of the pair will be an empty interval
             *         // TODO: use optional or variant for second argument
             */
            std::pair<IntervalT,IntervalT> getContractedInterval(const vb::VariableBounds<ConstraintT>& _bounds);

            carl::Variable getVariable();
            ConstraintT& getConstraint();

            friend inline std::ostream& operator <<(std::ostream& os, const ICPContractionCandidate& cc) {
                os << "(" << cc.mVariable << ", " << cc.mConstraint << ")";
                return os;
            }
    };
}
