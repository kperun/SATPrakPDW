#include "ICPState.h"
#include "ICPContractionCandidate.h"

namespace smtrat
{
    ICPState::ICPState() {
    }

    ICPState::~ICPState() {
    }

    BoxT& ICPState::getBox() {
        return mSearchBox;
    }

    void ICPState::setInterval(carl::Variable var, const IntervalT& interval) {
        mSearchBox[var] = interval;
    }

    IntervalT& ICPState::getInterval(carl::Variable var) {
        return mSearchBox[var];
    }

    ICPContractionCandidate& ICPState::getContractionCandidate() {
        return mContractionCandidate;
    }

    void ICPState::setContractionCandidate(const ICPContractionCandidate& contractionCandidate) {
        mContractionCandidate = contractionCandidate;
    }

    carl::Variable ICPState::getSplitDimension() {
        return mSplitDimension;
    }

    void ICPState::setSplitDimension(carl::Variable splitDimension) {
        mSplitDimension = splitDimension;
    }

    vector<ConstraintT>& ICPState::getConflictingConstraints() {
        return mConflictingConstraints;
    }

    void ICPState::addConflictingConstraint(const ConstraintT& constraint) {
        mConflictingConstraints.push_back(constraint);
    }
}