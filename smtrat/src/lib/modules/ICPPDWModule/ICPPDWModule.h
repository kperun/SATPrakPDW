/**
 * @file ICPPDWModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-04-27
 * Created on 2017-04-27.
 */

#pragma once

#include "../../solver/Module.h"
#include "../../datastructures/VariableBounds.h"
#include "ICPPDWStatistics.h"
#include "ICPPDWSettings.h"
#include "ICPTree.h"
#include "ICPContractionCandidate.h"
#include "ICPUtil.h"
#include "ICPPDWComperators.h"
#include <map>
#include <queue>

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
      //if a model exists, it should be stored here
      std::experimental::optional<Model> mFoundModel;

      // a map from constraints to formulas as required for the mInfeasibleSubset
      std::unordered_map<ConstraintT,FormulaT> mConstraintFormula;

      // the ICP search tree (root node)
      ICPTree<Settings> mSearchTree;

      // the set of original variables
      std::set<carl::Variable> mOriginalVariables;

      // the set of all active original constraints
      std::set<ConstraintT> mActiveOriginalConstraints;

      // all contraction candidates
      vector<ICPContractionCandidate<Settings>> mContractionCandidates;

      // only the contraction candidates which contain active constraints
      vector<ICPContractionCandidate<Settings>*> mActiveContractionCandidates;

      /**
       * We need to linearize constraints for ICP.
       * So we will store a map from original constraints to the linearized ones
       * and for convenience also a map from linearized constraints to original ones.
       * Note that we disregard monomial-slack substitution constraints
       * (that information can be retrieved from mMonomialSlackConstraints or mMonomialSubstitutions).
       *
       * The key set of mLinearizations also functions as the storage for the set of all linearized original constraints.
       */
      std::unordered_map<ConstraintT, ConstraintT> mLinearizations;
      std::unordered_map<ConstraintT, ConstraintT> mDeLinearizations;

      // the set of newly introduced variables (during the linearization)
      std::set<carl::Variable> mSlackVariables;

      // all slack substitutions constraints of the form "monomial - slack = 0"
      std::set<ConstraintT> mMonomialSlackConstraints;

      // a map from slack variables to the constraint of their substitution
      std::unordered_map<Poly, carl::Variable> mMonomialSubstitutions;

    private:
      /**
       * Returns a slack variable representing the given monomial.
       *
       * If this method is called for the first time for a given monomial, a new slack variable
       * will be created and associated with that monomial.
       * In all further calls, that slack variable is returned for the monomial.
       *
       * @param monomial a monomial
       * @return a slack variable representing that monomial
       */
      carl::Variable getSlackVariableForMonomial(Poly monomial);

      /**
       * Linearizes a constraint.
       *
       * E.g.: x*y + x*y*y + 5 = 0 will be linearized to
       *       a + b + 5 = 0 and x*y - a = 0 and x*y*y - b = 0
       *
       * The resulting constraints will be returned and stored in the mLinearizations and mDeLinearizations map.
       * The newly introduced variables will be added to mSlackVariables.
       * In case the constraint was linear, it will be mapped to itself.
       *
       * @param constraint The constraint that should be linearized
       */
      void linearizeConstraint(const ConstraintT& constraint);

      /**
       * Creates all contraction candidates.
       *
       * I.e. for every constraint that is stored in mDeLinearizations and every variable that occurs
       * in that constraint, a new constraction candidate will be created and stored in mContractionCandidates.
       */
      void createAllContractionCandidates();
      /**
       * Creates an infeasible subset if the problem is unsat.
       * The infeasible subset will added to the mInfeasableSubsets member.
       */
      void createInfeasableSubset();

      /**
       * Helper function which returns the delinearized constraint.
       * I.e., for a constraint r_1 + ... + r_k ~ 0, the original constraint m_1 + ... + m_k ~ 0 is returned.
       *
       * @param c a constraint
       * @return the de-linearized constraint if c was a linearized constraint, otherwise c itself
       */
      ConstraintT deLinearize(const ConstraintT& c);

      /**
       * Calls the backend with the handed over parameter.
       *
       * @param currentNode the current node containing all boundaries etc.
       * @return the answer as returned by the backend
       */
      Answer callBackend(ICPTree<Settings>* currentNode);


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


      /**
       * Tries to guess a solution and checks if all constraints are satisfied by that model.
       * If it finds a correct model, it will be returned. Otherwise, an empty optional will be returned.
       *
       * @param currentNode the ICP state of which a solution should be guessed
       * @return A correct model or optional empty
       */
      std::experimental::optional<Model> getSolution(ICPTree<Settings>* currentNode);

      void setModel(Model model);


      std::set<ConstraintT> getActiveOriginalConstraints();

#ifdef SMTRAT_DEVOPTION_Statistics
      ICPPDWStatistics* getStatistics(){return &mStatistics;}
#endif
  };
}
