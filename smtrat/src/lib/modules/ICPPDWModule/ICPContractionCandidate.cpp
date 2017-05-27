#include "ICPContractionCandidate.h"

namespace smtrat
{
  /**
   * We need a custom copy-constructor because Contractor is non-copyable...
   */
  ICPContractionCandidate::ICPContractionCandidate(const ICPContractionCandidate& rhs):
    mVariable(rhs.mVariable),
    mConstraint(rhs.mConstraint),
    mContractor(Contractor<carl::SimpleNewton>(rhs.mConstraint.lhs(), rhs.mConstraint.lhs())),
    mIsEqRelation(true)
  {
    constructorHelper();
  }

  ICPContractionCandidate::ICPContractionCandidate(const carl::Variable& var, const ConstraintT& constraint):
    mVariable(var),
    mConstraint(constraint),
    mContractor(constraint.lhs(), constraint.lhs()),
    mIsEqRelation(true)
  {
    constructorHelper();
  }

  void ICPContractionCandidate::constructorHelper(){
    //Special case if the relation is not EQ, since we can not use the predefined contraction
    if(mConstraint.relation() != carl::Relation::EQ){
      mIsEqRelation = false;
      //We only need to look at linear constraints, others are not used
      if(mConstraint.lhs().isLinear()){
        Poly p = mConstraint.lhs();
        Rational constantPart = 0;
				for (const auto& t: p) {
					if (t.has(mVariable)) {//The term that includes the var we are solving for
            //If the coefficient is negative we need to revert the relation
            //Unfortunately we can not use the inverse() function, since NEQ should not become EQ
            if(t.coeff() < 0){
              if(mConstraint.relation() == carl::Relation::LEQ){
                mNewRelation = carl::Relation::GEQ;
              } else if(mConstraint.relation() == carl::Relation::LESS) {
                mNewRelation = carl::Relation::GREATER;
              } else if(mConstraint.relation() == carl::Relation::GEQ) {
                mNewRelation = carl::Relation::LEQ;
              } else if(mConstraint.relation() == carl::Relation::GREATER) {
                mNewRelation = carl::Relation::LESS;
              }
            } else {
              mNewRelation = mConstraint.relation();
            }
					}
				}
      }else{ //These (original) constraints are generated but not used for contraction
      }
    }
  }

  ICPContractionCandidate::~ICPContractionCandidate() {
  }

  carl::Variable ICPContractionCandidate::getVariable() {
    return mVariable;
  }

  ConstraintT& ICPContractionCandidate::getConstraint() {
    return mConstraint;
  }

  double ICPContractionCandidate::getWeight(){
    return mWeight;
  }

  void ICPContractionCandidate::setWeight(double weight){
    mWeight = weight;
  }

  OneOrTwo<IntervalT> ICPContractionCandidate::getContractedInterval(const vb::VariableBounds<ConstraintT>& _bounds) {
    // first retrieve all variables with their respective bounds
    auto& map = _bounds.getIntervalMap();

    // possible are two intervals resulting from a split
    IntervalT originalInterval = _bounds.getDoubleInterval(mVariable);
    IntervalT resultA, resultB;
    std::experimental::optional<IntervalT> retB;

    //Two Cases: If the relation of the polynom is "=" we can simply use the Contractor.
    bool split = false;
    if (mConstraint.relation() == carl::Relation::EQ){
      // apply contraction
      // arguments are true because we want to use propagation
      bool split = mContractor(map, mVariable, resultA, resultB, true, true);
      // finally, we intersect the contracted interval with the original interval
      // This might not be necessary if it is already done in Contraction.
      resultA = resultA.intersect(originalInterval);
      resultB = resultB.intersect(originalInterval);
      if(split){ //Interval was split in two
        retB = resultB;
      } else { //only resultA
      }

      OneOrTwo<IntervalT> ret(resultA,retB);
      return ret;
    }
    else {//2nd case: Inequalities. This has to be handled as a special case.
      //First use the carl VarSolutionFormula to calculate the interval resulting from propagation
      carl::VarSolutionFormula<Poly> mySol(mConstraint.lhs(),mVariable);
      resultA = mySol.evaluate(map)[0]; //Should only contain one solution Interval
      //Next use the cases seen in slide 18 on ICP
      //TODO: Looking at all these cases is extremely tedious! This version ignores bounds that contain INFTY
      if(originalInterval.lowerBoundType() == carl::BoundType::INFTY
          || resultA.lowerBoundType() == carl::BoundType::INFTY
          || originalInterval.upperBoundType() == carl::BoundType::INFTY
          || resultA.upperBoundType() == carl::BoundType::INFTY){
        resultA = IntervalT::unboundedInterval();
        OneOrTwo<IntervalT> ret(resultA,retB);
        return ret;
      }

      switch(mNewRelation){
        case carl::Relation::LEQ:
          if(originalInterval.lower() >= resultA.upper()){
            resultA = IntervalT::emptyInterval();
          } else {
            resultA = IntervalT(originalInterval.lower(),carl::BoundType::WEAK,(originalInterval.upper() <= resultA.upper()?originalInterval.upper():resultA.upper()),carl::BoundType::WEAK);
          }
          break;
        case carl::Relation::LESS:
          resultA = IntervalT(originalInterval.lower(),carl::BoundType::WEAK,(originalInterval.upper() <= resultA.upper()?originalInterval.upper():resultA.upper()),carl::BoundType::WEAK);
          break;
        case carl::Relation::GEQ:
          resultA = IntervalT((originalInterval.lower() >= resultA.lower()?originalInterval.lower():resultA.lower()),carl::BoundType::WEAK, originalInterval.upper(),carl::BoundType::WEAK);
          break;
        case carl::Relation::GREATER:
          if(originalInterval.upper() <= resultA.lower()){
            resultA = IntervalT::emptyInterval();
          } else {
            resultA = IntervalT((originalInterval.lower() >= resultA.lower()?originalInterval.lower():resultA.lower()),carl::BoundType::WEAK, originalInterval.upper(),carl::BoundType::WEAK);
          }
          break;
        default:
          cout << "This should not happen" << endl;
          cout << mVariable << "," << mConstraint << endl;
          break;
      }
      cout << "Contracting from to: "<< endl;
      cout << originalInterval << endl;
      cout << resultA << endl;

      OneOrTwo<IntervalT> ret(resultA,retB);
      return ret;
    }
  }
}
