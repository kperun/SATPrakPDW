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

    ICPState::ICPState(const vb::VariableBounds<ConstraintT>& parentBounds) :
        mBounds(parentBounds),
        mAppliedContractionCandidates(),
        mAppliedIntervalConstraints(),
        mSplitDimension(),
        mConflictingConstraints()
    {
    }

    ICPState::~ICPState() {
    }

    vb::VariableBounds<ConstraintT>& ICPState::getBounds() {
        return mBounds;
    }

    void ICPState::setInterval(carl::Variable var, const IntervalT& interval) {
        // since we cannot directly set the interval for a variable,
        // we will need to add two constraints. one for the lower and one for the upper bound
        // one advantage of this approach is that we can easily revert a contraction
        // by removing those constraints from the variable bounds

        // since we cannot add unbounded constraints, we will simply ignore them
        vector<ConstraintT> intervalConstraints;

        // if upper bound is infty, the constraint is useless
        if (interval.upperBoundType() != carl::BoundType::INFTY) {
            // x <= upper bound
            // x - upper bound <= 0
            Poly upperPoly;
            upperPoly += var;
            upperPoly -= interval.upper();
            carl::Relation upperRelation = (interval.upperBoundType() == carl::BoundType::WEAK) ? carl::Relation::LEQ : carl::Relation::LESS;
            ConstraintT upperBound(upperPoly, upperRelation);
            intervalConstraints.push_back(upperBound);
        }

        // if lower bound is infty, the constraint is useless
        if (interval.lowerBoundType() != carl::BoundType::INFTY) {
            // x >= lower bound
            // lower bound - x <= 0
            Poly lowerPoly;
            lowerPoly -= var;
            lowerPoly += interval.lower();
            carl::Relation lowerRelation = (interval.lowerBoundType() == carl::BoundType::WEAK) ? carl::Relation::LEQ : carl::Relation::LESS;
            ConstraintT lowerBound(lowerPoly, lowerRelation);
            intervalConstraints.push_back(lowerBound);
        }

        addAppliedIntervalConstraint(intervalConstraints);
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

    vector<vector<ConstraintT>>& ICPState::getAppliedIntervalConstraints() {
        return mAppliedIntervalConstraints;
    }
    
    void ICPState::addAppliedIntervalConstraint(const ConstraintT& constraint) {
        vector<ConstraintT> intervalConstraints;
        intervalConstraints.push_back(constraint);
        mAppliedIntervalConstraints.push_back(intervalConstraints);
        mBounds.addBound(constraint, constraint);
    }

    void ICPState::addAppliedIntervalConstraint(const ConstraintT& lowerBound, const ConstraintT& upperBound) {
        vector<ConstraintT> intervalConstraints;
        intervalConstraints.push_back(lowerBound);
        intervalConstraints.push_back(upperBound);
        mAppliedIntervalConstraints.push_back(intervalConstraints);
        mBounds.addBound(lowerBound, lowerBound);
        mBounds.addBound(upperBound, upperBound);
    }
    
    void ICPState::addAppliedIntervalConstraint(const vector<ConstraintT>& constraints) {
        mAppliedIntervalConstraints.push_back(constraints);
        for (const ConstraintT& c : constraints) {
            mBounds.addBound(c, c);
        }
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

    bool ICPState::isUnsat() {
        return !mConflictingConstraints.empty();
    }
}
