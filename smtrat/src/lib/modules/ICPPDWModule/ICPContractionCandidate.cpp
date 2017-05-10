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
        //first retrieve all variables with their respective bounds
    	auto& map = _bounds.getIntervalMap();

        //possible are two intervals resulting from a split
        IntervalT resultA, resultB;

        // apply contraction
        // arguments are true because we want to use propagation
    	bool split = mContractor(map, mVariable, resultA, resultB, true, true);

        // TODO: the contractor thinks the constraints are equalities (poly = 0)
        //       but we can have <= as well. so deal with that (new rules, see slides)
        std::pair <IntervalT,IntervalT> ret(resultA,resultB);
        return ret;
    }
}
