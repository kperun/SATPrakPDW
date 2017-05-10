/*
 * File:   ContractionCandidate.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "../../datastructures/VariableBounds.h"
#include "carl/interval/Contraction.h"
#include <utility>  //for usage of std::pair

namespace smtrat
{
    typedef DoubleInterval IntervalT;

    /**
     * This class represents a contraction candidate (x, c) where x is a variable
     * and c is a constraint.
     */
    class ICPContractionCandidate
    {
        private:
            carl::Variable mVariable;
            ConstraintT mConstraint;
            //TODO byKosti
            //Contractor<carl::SimpleNewton>& mContractor;;//the contractor, currently it is on simple newton

        public:
            ICPContractionCandidate();
            ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint);
            ~ICPContractionCandidate();

            carl::Variable getVariable();
            void setVariable(const carl::Variable& var);

            ConstraintT& getConstraint();
            void setConstraint(const ConstraintT& constraint);



            //std::pair<IntervalT,IntervalT> TODO byKosti
            void getContractedInterval(const vb::VariableBounds<FormulaT>& _bounds,const carl::Variable& _variable);

            friend inline std::ostream& operator <<(std::ostream& os, const ICPContractionCandidate& cc) {
                os << "(" << cc.mVariable << ", " << cc.mConstraint << ")";
                return os;
            }
    };
}
