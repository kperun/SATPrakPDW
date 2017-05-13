#include "ICPState.h"
#include "ICPContractionCandidate.h"

namespace smtrat
{
    ICPState::ICPState() :
        mBounds(),
        mAppliedContractionCandidates(),
        mAppliedIntervalConstraints(),
        mConflictingConstraints()
    {
    }

    ICPState::ICPState(const vb::VariableBounds<ConstraintT>& parentBounds) :
        mBounds(parentBounds),
        mAppliedContractionCandidates(),
        mAppliedIntervalConstraints(),
        mConflictingConstraints()
    {
    }

    vb::VariableBounds<ConstraintT>& ICPState::getBounds() {
        return mBounds;
    }

    void ICPState::applyContraction(ICPContractionCandidate* cc, IntervalT interval) {
        addAppliedContractionCandidate(cc);
        setInterval(cc->getVariable(), interval, cc->getConstraint());
    }

    void ICPState::setInterval(carl::Variable var, const IntervalT& interval, const ConstraintT& _origin) {
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

        addAppliedIntervalConstraint(intervalConstraints, _origin);
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

    void ICPState::addAppliedIntervalConstraint(const ConstraintT& constraint, const ConstraintT& _origin) {
        vector<ConstraintT> intervalConstraints;
        intervalConstraints.push_back(constraint);
        mAppliedIntervalConstraints.push_back(intervalConstraints);
        mBounds.addBound(constraint, _origin);
    }

    void ICPState::addAppliedIntervalConstraint(const ConstraintT& lowerBound, const ConstraintT& upperBound, const ConstraintT& _origin) {
        vector<ConstraintT> intervalConstraints;
        intervalConstraints.push_back(lowerBound);
        intervalConstraints.push_back(upperBound);
        mAppliedIntervalConstraints.push_back(intervalConstraints);
        mBounds.addBound(lowerBound, _origin);
        mBounds.addBound(upperBound, _origin);
    }

    void ICPState::addAppliedIntervalConstraint(const vector<ConstraintT>& constraints, const ConstraintT& _origin) {
        mAppliedIntervalConstraints.push_back(constraints);
        for (const ConstraintT& c : constraints) {
            mBounds.addBound(c, _origin);
        }
    }

    std::set<ConstraintT>& ICPState::getConflictingConstraints() {
        return mConflictingConstraints;
    }

    void ICPState::setConflictingConstraints(const std::set<ConstraintT>& constraints) {
        mConflictingConstraints = constraints;
    }

    void ICPState::addConflictingConstraint(const ConstraintT& constraint) {
        mConflictingConstraints.insert(constraint);
    }

    bool ICPState::isUnsat() {
        return !mConflictingConstraints.empty();
    }

    bool ICPState::isTerminationConditionReached() {
        // TODO
        return mAppliedContractionCandidates.size() > ICPPDWSettings1::maxContractions;
    }

    ICPContractionCandidate& ICPState::getBestContractionCandidate(vector<ICPContractionCandidate>& contractionCandidates) {
        // TODO
        return contractionCandidates[0];
    }

    double ICPState::computeGain(smtrat::ICPContractionCandidate& candidate,const vb::VariableBounds<ConstraintT>& _bounds){
        //first compute the new interval
        OptionalInterval intervals = candidate.getContractedInterval(_bounds);
        //then retrieve the old one
        auto& map = _bounds.getIntervalMap();
        IntervalT old_interval = map.at(candidate.getVariable());
        //finally compute the diameter
        if(intervals.second){
            return 1 - ( (intervals.first.diameter()+intervals.second->diameter())/old_interval.diameter());
        }else{
            return 1 - ( intervals.first.diameter()/old_interval.diameter());
        }
        //Input:  Kriege einen kandidaten, das alte sowie das neue intervall.
        // 		1. schneide beide intervalle um das neue intervall zu berechnen.
        //		2. berechne 1- D_new/D_old <- hier müssen die diameter mit .diameter berechnet werden. returne den wert
        /*
            IntervalT new_inteval = evaluateIntervall(candidate);
            return 1 - (new_inteval.diameter()/old_interval.diameter());
        */
    }

    /*ICPContractionCandidate */ void ICPState::computeBestCandidate(/*std::list<ICPContractionCandidate> candidates*/){
        //Input: eine Liste an contraction candiate
        /*TODO:1.gehe durch die liste, für jeden kandiadaten berechne mit computeGain den gain.
        *	   2.speichere den aktuell größten gain zwischen und den CC zwischen. (als double und pointer)
        *	   3.wähle variable mit größten gain und gebe sie aus
        */
    }


}
