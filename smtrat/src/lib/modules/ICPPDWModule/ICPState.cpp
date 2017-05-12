#include "ICPState.h"
#include "ICPContractionCandidate.h"

namespace smtrat
{
    ICPState::ICPState() :
        mBounds(),
        mAppliedContractionCandidates(),
        mAppliedIntervalConstraints(),
        mSplitDimension(),
        mConflictingConstraints()
    {
    }

    ICPState::~ICPState() {
    }

    vb::VariableBounds<FormulaT>& ICPState::getBounds() {
        return mBounds;
    }

    void ICPState::setInterval(carl::Variable var, const IntervalT& interval) {
        // TODO
    }

    IntervalT ICPState::getInterval(carl::Variable var) {
        mBounds.getInterval(var);
    }

    vector<ICPContractionCandidate*>& ICPState::getAppliedContractionCandidates() {
        return mAppliedContractionCandidates;
    }

    void ICPState::addAppliedContractionCandidate(ICPContractionCandidate* contractionCandidate) {
        mAppliedContractionCandidates.push_back(contractionCandidate);
    }

    vector<std::pair<ConstraintT, ConstraintT>>& ICPState::getAppliedIntervalConstraints() {
        return mAppliedIntervalConstraints;
    }

    void ICPState::addAppliedIntervalConstraint(const ConstraintT& lowerBound, const ConstraintT& upperBound) {
        mAppliedIntervalConstraints.push_back(make_pair(lowerBound, upperBound));
    }

    carl::Variable ICPState::getSplitDimension() {
        return mSplitDimension;
    }

    void ICPState::setSplitDimension(carl::Variable splitDimension) {
        mSplitDimension = splitDimension;
    }

    std::set<ConstraintT>& ICPState::getConflictingConstraints() {
        return mConflictingConstraints;
    }

    void ICPState::addConflictingConstraint(const ConstraintT& constraint) {
        mConflictingConstraints.insert(constraint);
    }
}
