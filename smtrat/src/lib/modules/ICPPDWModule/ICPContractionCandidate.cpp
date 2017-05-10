#include "ICPContractionCandidate.h"

namespace smtrat
{
    /**
     * We need a custom copy-constructor because Contractor is non-copyable...
     */
    ICPContractionCandidate::ICPContractionCandidate(const ICPContractionCandidate& rhs):
        mVariable(rhs.mVariable),
        mConstraint(rhs.mConstraint),
        mContractor(Contractor<carl::SimpleNewton>(rhs.mConstraint.lhs(), rhs.mConstraint.lhs()))
    {
    }

    ICPContractionCandidate::ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint):
        mVariable(var),
        mConstraint(constraint),
        mContractor(Contractor<carl::SimpleNewton>(constraint.lhs(), constraint.lhs()))
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

    std::pair<IntervalT,IntervalT> ICPContractionCandidate::getContractedInterval(const vb::VariableBounds<FormulaT>& _bounds) {
        // first retrieve all variables with their respective bounds
    	auto& map = _bounds.getIntervalMap();

        // possible are two intervals resulting from a split
        IntervalT originalInterval = map.at(mVariable);
        IntervalT resultA, resultB;

        // apply contraction
        // arguments are true because we want to use propagation
    	bool split = mContractor(map, mVariable, resultA, resultB, true, true);

        // we need a case distinction for different relations
        // according to ICP slides from the lecture
        if (mConstraint.relation() == carl::Relation::EQ) {
            resultA = resultA.intersect(originalInterval);
            resultB = resultB.intersect(originalInterval);
        }
        else if(mConstraint.relation() == carl::Relation::LEQ) {
            // TODO: check if this is correct
            resultA = IntervalT(originalInterval.lower(), 
                                carl::getStrictestBoundType(originalInterval.lowerBoundType(), resultA.lowerBoundType()),
                                min(originalInterval.upper(), resultA.upper()), 
                                carl::getStrictestBoundType(originalInterval.upperBoundType(), resultA.upperBoundType()));
            resultB = IntervalT(originalInterval.lower(), 
                                carl::getStrictestBoundType(originalInterval.lowerBoundType(), resultB.lowerBoundType()),
                                min(originalInterval.upper(), resultB.upper()), 
                                carl::getStrictestBoundType(originalInterval.upperBoundType(), resultB.upperBoundType()));
        }
        else {
            // We don't need that because it's always == or <= ??
        }

        std::pair <IntervalT,IntervalT> ret(resultA,resultB);
        return ret;
    }
}
