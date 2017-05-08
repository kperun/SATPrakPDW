#include "ICPContractionCandidate.h"

namespace smtrat
{
    ICPContractionCandidate::ICPContractionCandidate() {
    }

    ICPContractionCandidate::ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint):
        mVariable(var),
        mConstraint(constraint)
    {
    }

    ICPContractionCandidate::~ICPContractionCandidate() {
    }

    carl::Variable ICPContractionCandidate::getVariable() {
        return mVariable;
    }

    void ICPContractionCandidate::setVariable(const carl::Variable& var) {
        mVariable = var;
    }

    ConstraintT& ICPContractionCandidate::getConstraint() {
        return mConstraint;
    }

    void ICPContractionCandidate::setConstraint(const ConstraintT& constraint) {
        mConstraint = constraint;
    }
}