/**
 * @file ICPPDWModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-04-27
 * Created on 2017-04-27.
 */

#pragma once

#include "../../solver/Module.h"
#include "ICPPDWStatistics.h"
#include "ICPPDWSettings.h"
#include "ICPTree.h"
#include "ICPContractionCandidate.h"

namespace smtrat
{
	template<typename Settings>
	class ICPPDWModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			ICPPDWStatistics mStatistics;
#endif
			// Members.

			// the ICP search tree
			ICPTree mSearchTree;
			// the initial ICP state
			ICPState mInitialState;

			// all contraction candidates
			vector<ICPContractionCandidate> mContractionCandidates;

			/**
			 * we need to linearize constraints for ICP
			 * so we will store a map from original constraints to the linearized ones
			 * and for convenience also a map from linearized constraints to original ones
			 */
			carl::FastMap<ConstraintT, vector<ConstraintT>> mLinearizations;
			carl::FastMap<ConstraintT,        ConstraintT > mDeLinearizations;

			// a list of newly introduced variables (during the linearization)
			vector<carl::Variable> mSlackVariables;
		
		private:
			/**
			 * Linearizes a constraint.
			 *
			 * E.g.: x*y + x*y*y + 5 = 0 will be linearized to
			 *       a + b + 5 = 0 and x*y - a = 0 and x*y*y - b = 0
			 *
			 * The resulting constraints will be returned and stored in the mLinearizations 
			 * and mDeLinearizations map.
			 * The newly introduced variables will be added to mSlackVariables.
			 * In case the constraint was linear, it will be mapped to itself.
			 *
			 * @param constraint The constraint that should be linearized
			 * @return A vector of resulting linearized constraints.
			 *         This vector is actually stored in the mLinearizations map.
			 */
			vector<ConstraintT>& linearizeConstraint(const ConstraintT& constraint);

			/**
			 * Creates/Retrieves an initial bound on am original variable.
			 *
			 * @param variable The original variable for which an initial bound should be created
			 */
			void createInitialVariableBound(const carl::Variable& variable);

			/**
			 * Creates an initial bound on a newly introduced slack variable.
			 * 
			 * This method will be called during the linearization process.
			 * The calculated initial bound will then be set as the current/initial bound for the slack variable.
			 *
			 * @param slackVariable The slack variable for which an initial bound should be created
			 * @param monomial The monomial for which this slack variable stands
			 *                 (i.e. the constraint slack = monomial was added during linearization)
			 */
			void createInitialSlackVariableBound(const carl::Variable& slackVariable, const Poly& monomial);

			double computeGain();
			void evaluateInterval();
			void computeBestCandidate();
			void transposeConstraint();
			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			ICPPDWModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);

			~ICPPDWModule();
			
			// Main interfaces.
			/**
			 * Informs the module about the given constraint. It should be tried to inform this
			 * module about any constraint it could receive eventually before assertSubformula
			 * is called (preferably for the first time, but at least before adding a formula
			 * containing that constraint).
			 * @param _constraint The constraint to inform about.
			 * @return false, if it can be easily decided whether the given constraint is inconsistent;
			 *		  true, otherwise.
			 */
			bool informCore( const FormulaT& _constraint );

			/**
			 * Informs all backends about the so far encountered constraints, which have not yet been communicated.
			 * This method must not and will not be called more than once and only before the first runBackends call.
			 */
			void init();

			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );

			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore( ModuleInput::const_iterator _subformula );

			/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
			void updateModel() const;

			/**
			 * Checks the received formula for consistency.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
	};
}
