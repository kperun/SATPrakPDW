#include "ICPState.h"

namespace smtrat
{
    ICPState::ICPState() {
    }

    ICPState::ICPState(ContractionCandidate* contractionCandidate) :
        mContractionCandidate(contractionCandidate)
    {
    }

    ICPState::~ICPState() {
    }

    std::map<carl::Variable*, RationalInterval>* ICPState::getBox() {
        return &mSearchBox;
    }

    ContractionCandidate* ICPState::getContractionCandidate() {
        return mContractionCandidate;
    }

    void ICPState::setContractionCandidate(ContractionCandidate* contractionCandidate) {
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