#include "ICPContractionCandidate.h"

namespace smtrat
{
    ICPContractionCandidate::ICPContractionCandidate() {
    }

    ICPContractionCandidate::ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint):
        mVariable(var),
        mConstraint(constraint)
    {
        //mContractor(e8_contractor(constraint.lhs()));//set the polynomial as the formula
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

    //std::pair<IntervalT,IntervalT> //TODO byKosti
    void ICPContractionCandidate::getContractedInterval(const vb::VariableBounds<FormulaT>& _bounds,const carl::Variable& _variable){
    	smtrat::EvalDoubleIntervalMap map = _bounds.getIntervalMap();//first retrieve all variables with their respective bounds
        /*
        Interval<double> resultA, resultB;//possible are two intervals resulting from a split
    	bool split = mContractor(map,_variable,resultA,resultB,true,true);
    	std::cout << "split = " << split << std::endl;
    	std::cout << "resultA = " << resultA << std::endl;
    	std::cout << "resultB = " << resultB << std::endl;
        std::pair <IntervalT,IntervalT> ret(resultA,resultB);
        return ret;
        */
    }



}
