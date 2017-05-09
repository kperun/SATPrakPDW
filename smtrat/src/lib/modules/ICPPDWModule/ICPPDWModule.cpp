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
	{
	}

	template<class Settings>
	ICPPDWModule<Settings>::~ICPPDWModule()
	{}

	
	template<class Settings>
	std::vector<ConstraintT>& ICPPDWModule<Settings>::linearizeConstraint(const ConstraintT& constraint, const FormulaT& _origin) {
		const Poly& polynomial = constraint.lhs();
		vector<ConstraintT> linearizedConstraints;

		if (polynomial.isLinear()) { // TODO: are polynomials with just one monome okay?
			// we don't need to do anything, so we simply map this constraint to itself
			linearizedConstraints.push_back(constraint);
		}
		else {
			// we need to actually linearize this constraint

			// this polynomial will contain the original polynomial,
			// but every non-linear term will have been replaced by a slack variable
			Poly linearizedOriginalPolynomial;

			// so we traverse every term
            for (const auto& term : polynomial.polynomial()) {
            	// we only need to linearize non-linear monomials
            	// we also need to check if the term is actually a monomial (it might be a constant)
            	if (term.monomial()) {

            		if (!term.monomial()->isLinear()) {
						/*
						 * Note: term == term.coeff() * term.monomial()
						 */
	            		Poly monomial = carl::makePolynomial<Poly>(Poly::PolyType(term.monomial()));

		            	// introduce a new slack variable representing that monomial
		            	carl::Variable slackVariable = carl::freshRealVariable();
		            	mSlackVariables.insert(slackVariable);

						// we create a new constraint (monomial - slack = 0) to connect the new slack variable with the monomial
						Poly slackPolynomial = monomial - slackVariable;
						ConstraintT slackConstraint(slackPolynomial, carl::Relation::EQ);

						addConstraintToBounds(slackConstraint,_origin);

						// replace that monomial in the original constraint by the slack variable
						// polynomial = c_1 * m_1 + ... + c_n * m_n
						// replaced to: c_1 * slack + ...
						linearizedOriginalPolynomial += term.coeff() * carl::makePolynomial<Poly>(slackVariable);

						// and add that new constraint to the resulting vector
						linearizedConstraints.push_back(slackConstraint);

						// we also need to calculate an initial bound on that new slack variable
						createInitialSlackVariableBound(slackVariable, monomial);
					}
	            }
	            else {
	            	linearizedOriginalPolynomial += term;
	            }
            }

            // finally, we add the linearized original constraint
            ConstraintT linearizedOriginalConstraint(linearizedOriginalPolynomial, constraint.relation());
            linearizedConstraints.push_back(linearizedOriginalConstraint);
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
	void ICPPDWModule<Settings>::createInitialVariableBound(const carl::Variable& variable) {
		// TODO
		// retrieve the inital bound of the given original variable and store it in mSearchTree.getCurrentState()
		IntervalT initialInterval(-42.0, 42.0);
		//mSearchTree.getCurrentState().setInterval(variable, initialInterval);
	}

	template<class Settings>
	void ICPPDWModule<Settings>::createInitialSlackVariableBound(const carl::Variable& slackVariable, const Poly& monomial) {
		// since slack = monomial, we simply need to evaluate the monomial with it's initial bounds
		// and then set the initial bound of the slack variable to the result
		IntervalT slackInterval = carl::IntervalEvaluation::evaluate(monomial, mBounds.getIntervalMap());

		// we also need to store those initial bounds in mInitialState.mSearchBox
		//mSearchTree.getCurrentState().setInterval(slackVariable, slackInterval);
	}



	template<class Settings>
	void ICPPDWModule<Settings>::createAllContractionCandidates() {
		// since we don't explicitly store all constraints, we need to iterate
		// over the key set of mDeLinearizations, since that map contains all constraints.

		for (const auto& mapIter : mDeLinearizations) {
			const ConstraintT& constraint = mapIter.first;

			// we create a new contraction candidate for every variable in that constraint
			for (const auto& variable : constraint.variables()) {
				ICPContractionCandidate candidate(variable, constraint);
			}
		}
	}


	template<class Settings>
	bool ICPPDWModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// we only consider actual constraints
		if (_constraint.getType() == carl::FormulaType::CONSTRAINT) {
			const ConstraintT& constraint = _constraint.constraint();

    		// retrieve the initial bound for all variables
    		for (const auto& var : constraint.variables()) {
    			mOriginalVariables.insert(var);
        		createInitialVariableBound(var);
        	}
			addConstraintToBounds(constraint,_constraint );

        	// linearize the constraints
			vector<ConstraintT>& newConstraints = linearizeConstraint(constraint,_constraint);

			// generates all contraction candidates, i.e. for every constraint c
			// it generates a pair of (var, c) for every variable that occurs in that constraint
			createAllContractionCandidates();

			// DEBUG
			std::cout << "Linearized constraints for " << constraint << ": " << std::endl;
			for (int i = 0; i < (int) newConstraints.size(); i++) {
				std::cout << newConstraints[i] << std::endl;
			}
        }
		return true; // This should be adapted according to your implementation.
	}

	template<class Settings>
	void ICPPDWModule<Settings>::init()
	{
		std::cout << "------------------------------------" << std::endl;
		std::cout << "All constraints informed.\n" << std::endl;
    	std::cout << "Initial original variable bounds: " << std::endl;
    	for (auto var = mOriginalVariables.begin(); var != mOriginalVariables.end(); var++) {
    		//std::cout << *var << " in " << mSearchTree.getCurrentState().getInterval(*var) << std::endl;
    	}
    	std::cout << "Initial slack variable bounds: " << std::endl;
    	for (auto var = mSlackVariables.begin(); var != mSlackVariables.end(); var++) {
    		//std::cout << *var << " in " << mSearchTree.getCurrentState().getInterval(*var) << std::endl;
    	}
		std::cout << "Initial original variable bound in mBounds" << std::endl;
		for(auto it = mBounds.getIntervalMap().begin(); it != mBounds.getIntervalMap().end(); ++it){
    		std::cout << it->first << " " << it->second << std::endl;
		}


	}

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


	template<class Settings>
	void ICPPDWModule<Settings>::addConstraintToBounds(const ConstraintT& _constraint, const FormulaT& _origin ){
		mBounds.addBound(_constraint,_origin);
	}

	template<class Settings>
	void ICPPDWModule<Settings>::removeConstraintFromBounds(const ConstraintT& _constraint, const FormulaT& _origin ){
		mBounds.removeBound(_constraint,_origin);
	}




	template<class Settings>
	double ICPPDWModule<Settings>::computeGain(/*ICPContractionCandidate* candidate, IntervalT old_interval*/){
		//Input:  Kriege einen kandidaten, das alte sowie das neue intervall.
		// 		1. schneide beide intervalle um das neue intervall zu berechnen.
		//		2. berechne 1- D_new/D_old <- hier müssen die diameter mit .diameter berechnet werden. returne den wert
		/*
			IntervalT new_inteval = evaluateIntervall(candidate);
			return 1 - (new_inteval.diameter()/old_interval.diameter());
		*/
	    return 0;
	}


	template<class Settings>
	/*IntervalT*/ void ICPPDWModule<Settings>::evaluateInterval(/*ICPContractionCandidate* candidate, */){
		//Input: ein Constraint candiadte bestehend aus einer variablen und einen constraint
		//TODO:1.nehme die variable und stelle im constraint die sachen nach dieser variablen um.
		//	   2.evaluiere das constraint in dem du die intervalle aller anderen variablen (die in der beobachteten menge)
		//	     drin sind einsetzt und ausrechnest (mit carl::IntrvalEvaluation::evaluate(candidate.var, candidate.constraint)??)
		//	   3.gebe zurück ein neues intervall, das jedoch noch nicht geschnitten wurde mit dem alten.
	}

	template<class Settings>
	/*ICPContractionCandidate */ void ICPPDWModule<Settings>::computeBestCandidate(/*std::list<ICPContractionCandidate> candidates*/){
		//Input: eine Liste an contraction candiate
		/*TODO:1.gehe durch die liste, für jeden kandiadaten berechne mit computeGain den gain.
		*	   2.speichere den aktuell größten gain zwischen und den CC zwischen. (als double und pointer)
		*	   3.wähle variable mit größten gain und gebe sie aus
		*/
	}

	template<class Settings>
	/* ConstraintT */ void ICPPDWModule<Settings>::transposeConstraint(/* ConstraintT* constraint, Variable* var */){
		/* Input: eine ConstraintT und ein Variable object
			TODO:1. hole das polynom raus mit:  const Poly& polynomial = constraint.lhs();
				 2. erstelle ein neues poly objekt.
				 3. prüfe mit constraint->hasVariable(var) ob die variable drin ist nach der man umstellen will
				 4. stelle von hand um (es gibt keine methode dafür). Vorgehen: gehe durch das constraint, entferne
				 	die variable die man betrachtet raus, setzte sie auf die rechte seite und invertiere das vorzeichen entsprechend
				 	in dem man ein neues poly erstellt mit der var und einen - davor.
				 5. prüfe dass der operator nicht nicht == und nicht != ist, wenn es so ist dann negiere ihn wenn - vor der variable steht.
		*/
	}





}

#include "Instantiation.h"
