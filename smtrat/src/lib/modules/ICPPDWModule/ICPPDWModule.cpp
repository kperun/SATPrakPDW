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
		Module( _formula, _conditionals, _manager ),
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics(Settings::moduleName),
#endif
		mSearchTree(),
		mLeafNodes(),
		mOriginalVariables(),
		mContractionCandidates(),
		mLinearizations(),
		mDeLinearizations(),
		mSlackVariables(),
		mActiveOriginalConstraints(),
		mSlackSubstitutionConstraints()
	{
		mLeafNodes.push(&mSearchTree);
	}

	template<class Settings>
	ICPPDWModule<Settings>::~ICPPDWModule()
	{}


	template<class Settings>
	std::vector<ConstraintT>& ICPPDWModule<Settings>::linearizeConstraint(const ConstraintT& constraint, const FormulaT& _origin) {
		const Poly& polynomial = constraint.lhs();

		// this vector stores all generated linearized constraints that will actually be used during ICP
		vector<ConstraintT> linearizedConstraints;


		if (polynomial.isLinear()) {
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
	            		Poly monomial(term.monomial());

		            	// introduce a new slack variable representing that monomial
		            	carl::Variable slackVariable = carl::freshRealVariable();
		            	mSlackVariables.insert(slackVariable);

						// we create a new constraint (monomial - slack = 0) to connect the new slack variable with the monomial
						Poly slackPolynomial = monomial - slackVariable;
						ConstraintT slackConstraint(slackPolynomial, carl::Relation::EQ);

						// replace that monomial in the original constraint by the slack variable
						// polynomial = c_1 * m_1 + ... + c_n * m_n
						// replaced to: c_1 * slack + ...
						linearizedOriginalPolynomial += term.coeff() * carl::makePolynomial<Poly>(slackVariable);

						// and add that new constraint to the resulting vector
						linearizedConstraints.push_back(slackConstraint);

						// we also need to store the substitution we made so that we can initialize the slack bounds
						mSlackSubstitutionConstraints[slackVariable] = slackConstraint;
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

		// after we generated all constraints that will actually be used
		// we store the mapping of original constraint to linearized constraints
		mLinearizations[constraint] = linearizedConstraints;
		for (const auto& lC : linearizedConstraints) {
			mDeLinearizations[lC] = constraint;
		}

		return mLinearizations[constraint];
	}


	template<class Settings>
	void ICPPDWModule<Settings>::createAllContractionCandidates() {
		// since we don't explicitly store all constraints, we need to iterate
		// over the key set of mDeLinearizations, since that map contains all constraints.
		for (const auto& mapIter : mDeLinearizations) {
			const ConstraintT& constraint = mapIter.first;

			// if the constraint only contains one variable, we cannot use it for contraction
			if (constraint.variables().size() > 1) {
				// we create a new contraction candidate for every variable in that constraint
				for (const auto& variable : constraint.variables()) {
					mContractionCandidates.push_back(ICPContractionCandidate(variable, constraint));
				}
			}
		}
	}

	template<class Settings>
	void ICPPDWModule<Settings>::initBounds() {
		// the bounds for original variables have been added through addCore already

		// we only need to update bounds for slack variables in this method
		std::cout << "Init bounds: " << std::endl;
		for (const auto& mapEntry : mSlackSubstitutionConstraints) {
			const carl::Variable slackVar = mapEntry.first;
			const ConstraintT& slackConstraint = mapEntry.second;

			Contractor<carl::SimpleNewton> evaluator(slackConstraint.lhs());
			// we can ignore the second interval since contracting monome = slack for slack never results in splits
	        IntervalT initialInterval, ignore;
	    	evaluator(mSearchTree.getCurrentState().getBounds().getIntervalMap(), slackVar, initialInterval, ignore, true, true);
			mSearchTree.getCurrentState().setInterval(slackVar, initialInterval, slackConstraint);
		}
	}


	template<class Settings>
	bool ICPPDWModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// we only consider actual constraints
		if (_constraint.getType() == carl::FormulaType::CONSTRAINT) {
			const ConstraintT& constraint = _constraint.constraint();

			// store all variables we see for book-keeping purposes
    		for (const auto& var : constraint.variables()) {
    			mOriginalVariables.insert(var);
        	}

        	// linearize the constraints
			vector<ConstraintT>& newConstraints = linearizeConstraint(constraint, _constraint);

			// TODO (if contraction with INFTY doesn't work)
			// initSlackBounds() // applies contraction to determine initial slack bounds

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
		// generates all contraction candidates, i.e. for every constraint c
		// it generates a pair of (var, c) for every variable that occurs in that constraint
		createAllContractionCandidates();

		// DEBUG
		std::cout << "------------------------------------" << std::endl;
		std::cout << "All constraints informed.\n" << std::endl;

		std::cout << "Contraction Candidates:" << std::endl;
		for (const auto& cc : mContractionCandidates) {
			std::cout << cc << std::endl;
		}
	}

	template<class Settings>
	bool ICPPDWModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		const FormulaT& formula = _subformula->formula();
		// we only consider actual constraints
		if (formula.getType() == carl::FormulaType::CONSTRAINT) {
			const ConstraintT& constraint = formula.constraint();

			// A constraint was activated
			mActiveOriginalConstraints.insert(constraint);

			// we need to activate the bounds for that constraint
			// since we linearized the constraints, we actually need to activate
			// the linearized constraints instead of the original one
			for (const auto& lC : mLinearizations[constraint]) {
				addConstraintToBounds(lC, constraint);
			}
		}

		return true; // This should be adapted according to your implementation.
	}

	template<class Settings>
	void ICPPDWModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		const FormulaT& formula = _subformula->formula();
		// we only consider actual constraints
		if (formula.getType() == carl::FormulaType::CONSTRAINT) {
			const ConstraintT& constraint = formula.constraint();

			// A constraint was de-activated
			mActiveOriginalConstraints.erase(constraint);

			// we need to de-activate the bounds for that constraint
			// since we linearized the constraints, we actually need to remove
			// the linearized constraints instead of the original one
			for (const auto& lC : mLinearizations[constraint]) {
				removeConstraintFromBounds(lC, constraint);
			}

			// TODO: go through the search tree and remove sub-trees where this constraint was used
		}
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
		// initialize the bounds of all variables
		// we are initializing them during checkCore and not duringInit,
		// because we cannot distinguish between constraints that were added by the boolean solver
		// and might be removed later and constraints which correspond to initial bounds for variables
		// during checkCore we can be sure that all necessary constraints have been added already
		initBounds();

		// DEBUG
		std::cout << "------------------------------------" << std::endl;
		std::cout << "Check core with the following active constraints:\n" << std::endl;
		for (const auto& c : mActiveOriginalConstraints) {
			for (const auto& lC : mLinearizations[c]) {
				std::cout << lC << std::endl;
			}
		}

		// main loop of the algorithm
		// we can search for a solution as long as there still exist leaf nodes
		// which have not been fully contracted yet
		while (!mLeafNodes.empty()) {
			// simply take the first one and contract it
			ICPTree* currentNode = mLeafNodes.top();
			mLeafNodes.pop();

			// contract() will contract the node until a split occurs,
			// or the bounds turn out to be UNSAT,
			// or some other termination criterium was met (e.g. target diameter of intervals)
			bool splitOccurred = currentNode->contract(mContractionCandidates);

			if (splitOccurred) {
				// a split occurred, so add the new child nodes to the leaf nodes stack
				mLeafNodes.push(currentNode->getLeftChild());
				mLeafNodes.push(currentNode->getRightChild());

				// and then we continue with some other leaf node in the next iteration
				// this corresponds to depth-first search
				// later maybe: use multithreading to contract several leaf nodes at once
			}
			else {
				// we stopped not because of a split, but because the bounds
				// are either UNSAT or some abortion criterium was met
				if (currentNode->getCurrentState().isUnsat()) {
					std::cout << "Current ICP State is UNSAT." << std::endl;
				}
				else {
					// a termination criterium was met
					// so we try to guess a solution
          map<carl::Variable,double> sol(currentNode->getCurrentState().guessSolution());
          Model model;
          std::cout << "Guessed solution:" << std::endl;
          for(auto& clause : sol){
            cout << clause.first << ":" << clause.second << endl;
            Rational val = carl::rationalize<Rational>(clause.second);
            model.emplace(clause.first, val);
          }
          bool doesSat = true;
          for( const auto& rf : rReceivedFormula() )
          {
            cout << rf.formula().constraint() << endl;
            // TODO: This check is incomplete? Refer to ICPModule
            unsigned isSatisfied = carl::model::satisfiedBy(rf.formula().constraint(), model);
            cout << isSatisfied << endl;
            assert(isSatisfied != 2);
            if(isSatisfied == 0 || isSatisfied == 2){
              doesSat = false;
              break;
            }
          }
          if(doesSat){
            cout << "Found Model, returning SAT" << endl;
            return Answer::SAT;
          } else {
            // we don't know, since ICP is not complete.
            // maybe later: call CAD backend
            // but for now, we simply don't know
            // if no leaf node knows an answer, we will return UNKNOWN
            // after this main loop
            cout << "No Model could be guessed, returning UNKNOWN" << endl;
          }
				}
			}
		}

		// we have left the main loop
		// this means we have fully contracted every ICP node in our search tree
		// if every node turned out to be UNSAT, the root node will now be UNSAT as well
		if (mSearchTree.getCurrentState().isUnsat()) {
			std::cout << "Reasons: " << std::endl;
            for (const ConstraintT& c : mSearchTree.getCurrentState().getConflictingConstraints()) {
                std::cout << mDeLinearizations[c] << ", ";
            }
            std::cout << std::endl;

			return Answer::UNSAT;
		}
		else {
			// we would have returned SAT within the main loop,
			// so if after the main loop the problem is not UNSAT,
			// we simply don't know the answer
			return Answer::UNKNOWN;
		}
	}


	template<class Settings>
	void ICPPDWModule<Settings>::addConstraintToBounds(const ConstraintT& _constraint, const ConstraintT& _origin ){
		mSearchTree.getCurrentState().getBounds().addBound(_constraint,_origin);
	}

	template<class Settings>
	void ICPPDWModule<Settings>::removeConstraintFromBounds(const ConstraintT& _constraint, const ConstraintT& _origin ){
		mSearchTree.getCurrentState().getBounds().removeBound(_constraint,_origin);
	}
}

#include "Instantiation.h"
