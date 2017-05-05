/**
 * @file ICPPDW.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-04-27
 * Created on 2017-04-27.
 */

#include "ICPPDWModule.h"
#include "ICPContractionCandidate.h"
#include "ICPState.h"

namespace smtrat
{
	template<class Settings>
	ICPPDWModule<Settings>::ICPPDWModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	ICPPDWModule<Settings>::~ICPPDWModule()
	{}

	template<class Settings>
	vector<ConstraintT>& ICPPDWModule<Settings>::linearizeConstraint(const ConstraintT& constraint) {
		const Poly& polynomial = constraint.lhs();
		vector<ConstraintT> linearizedConstraints;

		if (polynomial.isLinear()) { // TODO: are polynomials with just one monome okay?
			// we don't need to do anything, so we simply map this constraint to itself
			linearizedConstraints.push_back(constraint);
		}
		else {
			// we need to actually linearize this constraint

			// so we traverse every monomial (product of variables)
            for (auto monomial = polynomial.polynomial().begin(); monomial != polynomial.polynomial().end(); monomial++) {
            	// we only need to linearize non-linear monomials
            	if (! monomial->monomial()->isLinear()) {

	            	// introduce a new slack variable representing that monomial
	            	carl::Variable slackVariable = carl::freshRealVariable();
	            	mSlackVariables.push_back(slackVariable);

					// we create a new constraint to connect the new slack variable with the monomial
					// TODO: needs to be: slack - monome = 0
					Poly slackPolynomial;
					ConstraintT slackConstraint(slackPolynomial, carl::Relation::EQ);

					// and add that new constraint to the resulting vector
					linearizedConstraints.push_back(slackConstraint);

					// we also need to calculate an initial bound on that new slack variable
					// TODO
	            }
            }
		}

		// fill the maps so that we know how we linearized this constraint
		mLinearizations[constraint] = linearizedConstraints;
		for (int i = 0; i < (int) linearizedConstraints.size(); i++) {
			ConstraintT c = linearizedConstraints[i];
			mDeLinearizations[c] = constraint;
		}

		return mLinearizations[constraint];
	}
	
	template<class Settings>
	bool ICPPDWModule<Settings>::informCore( const FormulaT& _constraint )
	bool ICPPDWModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// we only consider actual constraints
		if (_constraint.getType() == carl::FormulaType::CONSTRAINT) {
			const ConstraintT& constraint = _constraint.constraint();

			// pre-processing
			vector<ConstraintT>& newConstraints = linearizeConstraint(constraint);

			// DEBUG
			std::cout << "Linearized constraints for " << constraint << std::endl;
			for (int i = 0; i < (int) newConstraints.size(); i++) {
				std::cout << newConstraints[i] << std::endl;
			}
        }
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void ICPPDWModule<Settings>::init()
	{}
	
	template<class Settings>
	bool ICPPDWModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void ICPPDWModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void ICPPDWModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer ICPPDWModule<Settings>::checkCore()
	{
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}


	double computeGain(ICPContractionCandidate* candidate){
		//1 - D_new/D_old
		return 0.0;
	}

}

#include "Instantiation.h"
