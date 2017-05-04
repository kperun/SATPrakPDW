#include "ContractionCandidate.h"

namespace smtrat
{
    carl::Variable* ContractionCandidate::getVariable() {
        return mVariable;
    }

    void ContractionCandidate::setVariable(carl::Variable* var) {
        mVariable = var;
    }

    const ConstraintT* ContractionCandidate::getConstraint() {
        return mConstraint;
    }

    void ContractionCandidate::setConstraint(const ConstraintT* constraint) {
        mConstraint = constraint;
    }
}