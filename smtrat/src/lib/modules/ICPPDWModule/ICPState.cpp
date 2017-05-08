#include "ICPState.h"
#include "ICPContractionCandidate.h"

namespace smtrat
{
    ICPState::ICPState() {
    }

    ICPState::ICPState(ICPContractionCandidate* contractionCandidate) :
        mContractionCandidate(contractionCandidate)
    {
    }

    ICPState::~ICPState() {
    }

    BoxT* ICPState::getBox() {
        return &mSearchBox;
    }

    void ICPState::setInterval(const carl::Variable& var, const RationalInterval& interval) {
        mSearchBox[var] = interval;
    }

    ICPContractionCandidate* ICPState::getContractionCandidate() {
        return mContractionCandidate;
    }

    void ICPState::setContractionCandidate(ICPContractionCandidate* contractionCandidate) {
        mContractionCandidate = contractionCandidate;
    }

    carl::Variable* ICPState::getSplitDimension() {
        return mSplitDimension;
    }

    void ICPState::setSplitDimension(carl::Variable* splitDimension) {
        mSplitDimension = splitDimension;
    }

    vector<ConstraintT*>* ICPState::getConflictingConstraints() {
        return &mConflictingConstraints;
    }

    void ICPState::addConflictingConstraint(ConstraintT* constraint) {
        mConflictingConstraints.push_back(constraint);
    }
}