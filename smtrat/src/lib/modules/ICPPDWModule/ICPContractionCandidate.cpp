#include "ICPContractionCandidate.h"

namespace smtrat
{
    carl::Variable& ICPContractionCandidate::getVariable() {
        return mVariable;
    }

    void ICPContractionCandidate::setVariable(carl::Variable& var) {
        mVariable = var;
    }

    ConstraintT& ICPContractionCandidate::getConstraint() {
        return mConstraint;
    }

    void ICPContractionCandidate::setConstraint(const ConstraintT& constraint) {
        mConstraint = constraint;
    }
}