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
        if(mAppliedContractionCandidates.size() > ICPPDWSettings1::maxContractions){
            std::cout << "Termination reached by max iterations\n";
            return true;
        }
        //otherwise check if we have reached our desired interval
        auto& map = mBounds.getIntervalMap();
        //first check if all intervals are inside the desired one
        for (const auto &keyValue : map ) {
            if(keyValue.second.diameter()>ICPPDWSettings1::targetInterval){
                return false;
            }
        }
        //if all intervals are ok, just terminate
        std::cout << "Termination reached by desired interval\n";
        return true;


    }

    double ICPState::computeGain(smtrat::ICPContractionCandidate& candidate,vb::VariableBounds<ConstraintT>& _bounds){
        //first compute the new interval
        OptionalInterval intervals = candidate.getContractedInterval(_bounds);
        //then retrieve the old one
        auto& map = _bounds.getIntervalMap();
        IntervalT old_interval = map.at(candidate.getVariable());

        //in order to avoid manipulation of the existing objects, we work here with retrieved values
        //moreover, we use a bigM in order to be able to compute with -INF and INF
        double newFirstLower = 0;
        double newFirstUpper = 0;
        double newSecondLower = 0;
        double newSecondUpper = 0;
        double oldIntervalLower = 0;
        double oldIntervalUpper = 0;
        //first the mandatory first interval
        if(intervals.first.lowerBoundType()== carl::BoundType::INFTY){
            newFirstLower = -ICPPDWSettings1::bigM;
        }else{
            newFirstLower = intervals.first.lower();
        }

        if(intervals.first.upperBoundType()== carl::BoundType::INFTY){
            newFirstUpper = ICPPDWSettings1::bigM;
        }else{
            newFirstUpper = intervals.first.upper();
        }

        //now the second optional interval
        if(intervals.second){
            if((*(intervals.second)).lowerBoundType()== carl::BoundType::INFTY){
                newSecondLower = -ICPPDWSettings1::bigM;
            }else{
                newSecondLower = (*(intervals.second)).lower();
            }

            if((*(intervals.second)).upperBoundType()== carl::BoundType::INFTY){
                newSecondUpper = ICPPDWSettings1::bigM;
            }else{
                newSecondUpper = (*(intervals.second)).upper();
            }
        }
        //finally the old interval
        if(old_interval.lowerBoundType()== carl::BoundType::INFTY){
            oldIntervalLower = -ICPPDWSettings1::bigM;
        }else{
            oldIntervalLower = old_interval.lower();
        }

        if(old_interval.upperBoundType()== carl::BoundType::INFTY){
            oldIntervalUpper = ICPPDWSettings1::bigM;
        }else{
            oldIntervalUpper = old_interval.upper();
        }
        if(false){
            std::cout << "New1: "<< newFirstLower <<" : "<<newFirstUpper<<"\n";
            std::cout << "New2: "<< newSecondLower <<" : "<<newSecondUpper<<"\n";
            std::cout << "Old: "<< oldIntervalLower <<" : "<<oldIntervalUpper<<"\n";
        }
        //return the value
        return 1 -((newFirstUpper-newFirstLower)+(newSecondUpper-newSecondLower))/(oldIntervalUpper-oldIntervalLower);
    }

    ICPContractionCandidate& ICPState::getBestContractionCandidate(vector<ICPContractionCandidate>& candidates){
        if(candidates.size()==0){
            throw std::invalid_argument( "Candidates vector is empty!" );
        }

        std::cout << "----------------------------------------- \n";
        //in the case that the list has only one element, return this one element
        if(candidates.size()==1){
            return candidates.front();//return the first element
        }
        //store the current best candidate index
        int currentBest = 0;

        double currentBestGain = 0;

        for (int it = 0; it < (int) candidates.size(); it++) {
            std::cout << "----------------------------------------- \n";
            std::cout << "Current best gain: "<<currentBestGain << "\n";
            std::cout << "Current gain for " << candidates[it] << ": "<< computeGain(candidates[it],mBounds) << "\n";

            if(computeGain(candidates[it],mBounds)>computeGain(candidates[currentBest],mBounds)){
                //now set the new best candidate as current
                currentBestGain = computeGain(candidates[it],mBounds);
                currentBest = it;
            }
        }
        std::cout << "-------------------Final----------------- \n";
        std::cout << "Overall best gain: " <<currentBestGain << "\n";
        std::cout << "----------------------------------------- \n";
        return candidates[currentBest];
    }


}
