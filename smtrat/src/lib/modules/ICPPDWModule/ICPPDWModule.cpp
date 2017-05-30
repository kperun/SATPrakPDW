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
#include "ICPUtil.h"

namespace smtrat
{

  template<class Settings>
    ICPPDWModule<Settings>::ICPPDWModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager) :
      Module( _formula, _conditionals, _manager ),
#ifdef SMTRAT_DEVOPTION_Statistics
      mStatistics(Settings::moduleName),
#endif
      mFoundModel(),
      mConstraintFormula(),
      mOriginalVariables(),
      mSearchTree(&mOriginalVariables,this),
      mContractionCandidates(),
      mLinearizations(),
      mDeLinearizations(),
      mSlackVariables(),
      mActiveOriginalConstraints(),
      mSlackSubstitutionConstraints(),
      mActiveContractionCandidates()
      {
      }

  template<class Settings>
    ICPPDWModule<Settings>::~ICPPDWModule()
    {
    }


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

      // and for convenience also a mapping of linearized constraints to original constraints
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
    bool ICPPDWModule<Settings>::informCore( const FormulaT& _constraint )
    {
      // we only consider actual constraints
      if (_constraint.getType() == carl::FormulaType::CONSTRAINT) {
        const ConstraintT& constraint = _constraint.constraint();

        //first add it to the map between constraints and formulas
        mConstraintFormula[constraint] = _constraint;

        // store all variables we see for book-keeping purposes
        for (const auto& var : constraint.variables()) {
          mOriginalVariables.insert(var);
        }

        // linearize the constraints
        vector<ConstraintT>& newConstraints = linearizeConstraint(constraint, _constraint);

#ifdef PDW_MODULE_DEBUG_1
        // DEBUG
        std::cout << "Linearized constraints for " << constraint << ": ";
        for (int i = 0; i < (int) newConstraints.size(); i++) {
          std::cout << newConstraints[i] << endl;
        }
        std::cout << "" << endl;
#endif
      }
      return true; // This should be adapted according to your implementation.
    }

  template<class Settings>
    void ICPPDWModule<Settings>::init()
    {
      // generates all contraction candidates, i.e. for every constraint c
      // it generates a pair of (var, c) for every variable that occurs in that constraint
      createAllContractionCandidates();
#ifdef PDW_MODULE_DEBUG_1
      // DEBUG
      std::cout <<  "------------------------------------\nAll constraints informed.\n" << std::endl;

      std::cout << "Contraction Candidates:";
      for (const auto& cc : mContractionCandidates) {
        std::cout <<  cc;
      }
      std::cout << std::endl;
#endif
    }

  template<class Settings>
    bool ICPPDWModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
      const FormulaT& formula = _subformula->formula();

      // we only consider actual constraints
      bool causesConflict = false;
      if (formula.getType() == carl::FormulaType::CONSTRAINT) {
        const ConstraintT& constraint = formula.constraint();
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "Adding core: " << constraint << std::endl;
#endif
        // A constraint was activated
        mActiveOriginalConstraints.insert(constraint);

        // we need to activate the bounds for that constraint
        // since we linearized the constraints, we actually need to activate
        // the linearized constraints instead of the original one
        for (const auto& lC : mLinearizations[constraint]) {
          for (auto& cc : mContractionCandidates) {
            if (cc.getConstraint() == lC) {
              mActiveContractionCandidates.push_back(&cc);
            }
          }

          // we actually add the constraint to our search tree
          if(!mSearchTree.addConstraint(lC, constraint)) {
            causesConflict = true;
          }
        }
      }

      return !causesConflict;
    }

  template<class Settings>
    void ICPPDWModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
      const FormulaT& formula = _subformula->formula();
      // we only consider actual constraints
      if (formula.getType() == carl::FormulaType::CONSTRAINT) {
        const ConstraintT& constraint = formula.constraint();

#ifdef PDW_MODULE_DEBUG_1
        std::cout <<  "Removing core: " << constraint << std::endl;
#endif
        // A constraint was de-activated
        auto cIt = std::find(mActiveOriginalConstraints.begin(), mActiveOriginalConstraints.end(), constraint);
        if (cIt != mActiveOriginalConstraints.end()) {
          mActiveOriginalConstraints.erase(cIt);
        }

        // we need to de-activate the bounds for that constraint
        // since we linearized the constraints, we actually need to remove
        // the linearized constraints instead of the original one
        for (const auto& lC : mLinearizations[constraint]) {
          for (auto& cc : mContractionCandidates) {
            if (cc.getConstraint() == lC) {
              auto ccIt = std::find(mActiveContractionCandidates.begin(), mActiveContractionCandidates.end(), &cc);
              if (ccIt != mActiveContractionCandidates.end()) {
                mActiveContractionCandidates.erase(ccIt);
              }
            }
          }

          // we actually remove the constraint from within our search tree
          mSearchTree.removeConstraint(lC, constraint);
        }
      }
    }

  template<class Settings>
    void ICPPDWModule<Settings>::updateModel() const {
      mModel.clear();
      if( solverState() == Answer::SAT ) { //if a solution has been found by the guess routine
        //update the model by the currently stored one
        mModel.update((*mFoundModel));
      }
    }

  template<class Settings>
    Answer ICPPDWModule<Settings>::checkCore(){
#ifdef SMTRAT_DEVOPTION_Statistics
    mStatistics.increaseNumberOfIterations();
#endif
#ifdef PDW_MODULE_DEBUG_1
      std::cout << "------------------------------------\n"
        << "Check core with the following active original constraints:\n";
      for (const auto& c : mActiveOriginalConstraints) {
        for (const auto& lC : mLinearizations[c]) {
          std::cout <<  lC;
        }
      }
      std::cout <<  "" ;

      std::cout <<  "Check core with the following active contraction candidates:\n";
      for (const auto& cc : mActiveContractionCandidates) {
        std::cout << *cc << std::endl;
      }
      std::cout << "" << std::endl;
#endif
      // clean up first
      // reset the found model for the next iteration
      mFoundModel = std::experimental::nullopt;

      // we need to search through all leaf nodes of the search tree, store them in a priority queue
      std::priority_queue<ICPTree<Settings>*,std::vector<ICPTree<Settings>*>,std::function<bool(ICPTree<Settings>*, ICPTree<Settings>*)>> searchPriorityQueue(ICPTree<Settings>::compareTrees);

      vector<ICPTree<Settings>*> leafNodes = mSearchTree.getLeafNodes();
      for (ICPTree<Settings>* i : leafNodes) {
        searchPriorityQueue.push(i);
      }

      // main loop of the algorithm
      // we can search for a solution as long as there still exist leaf nodes
      // which have not been fully contracted yet
      while (!searchPriorityQueue.empty()) {
        // simply take the first one and contract it
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "ICPStates left to check: " << searchPriorityQueue.size() << std::endl;
#endif
        ICPTree<Settings>* currentNode = searchPriorityQueue.top();
        searchPriorityQueue.pop();

        // contract() will contract the node until a split occurs,
        // or the bounds turn out to be UNSAT,
        // or some other termination criterium was met (e.g. target diameter of intervals)
        bool splitOccurred = currentNode->contract(mActiveContractionCandidates,this);

        if (splitOccurred) {
#ifdef SMTRAT_DEVOPTION_Statistics
          mStatistics.increaseNumberOfSplits();
#endif
          // a split occurred, so add the new child nodes to the leaf nodes stack
          searchPriorityQueue.push(currentNode->getLeftChild());
          searchPriorityQueue.push(currentNode->getRightChild());
#ifdef SMTRAT_DEVOPTION_Statistics
          mStatistics.increaseNumberOfNodes();
          mStatistics.increaseNumberOfNodes();
#endif
          // and then we continue with some other leaf node in the next iteration
          // this corresponds to depth-first search
          // later maybe: use multithreading to contract several leaf nodes at once
        }else {
          // we stopped not because of a split, but because the bounds
          // are either UNSAT or some abortion criterium was met
          if (currentNode->isUnsat()) {
#ifdef PDW_MODULE_DEBUG_1
            std::cout << "Current ICP State is UNSAT." << std::endl;
#endif
          }
          else {
            // a termination criterium was met
            // so we try to guess a solution
            std::experimental::optional<Model> model;
            if(!mFoundModel){
              model = getSolution(currentNode);
            }else {//now if we have guessed a solution in the ICPTree contract method in order to avoid splits, we use it here
              model = mFoundModel;
            }
            if(model) {
#ifdef PDW_MODULE_DEBUG_1
              std::cout << "------------------------------" << std::endl
                  << "Final Answer: SAT." << std::endl;
#endif
              //now it is sat, thus store a pointer to the model
              mFoundModel = *model;
              return Answer::SAT;
            } else {
              // we don't know, since ICP is not complete.
              // maybe later: call CAD backend
              // but for now, we simply don't know
              // if no leaf node knows an answer, we will return UNKNOWN
              // after this main loop
#ifdef PDW_MODULE_DEBUG_1
              std::cout << "No Model could be guessed, returning UNKNOWN" << std::endl
                  << "------------------------------\n";
#endif
            }
          }
        }
      }

      // we have left the main loop
      // this means we have fully contracted every ICP node in our search tree
      // if every node turned out to be UNSAT, the root node will now be UNSAT as well
      if (mSearchTree.isUnsat()) {
        // we need to create an infeasible subset for the governing algorithm
        // otherwise the sat solver will not determine UNSAT
        createInfeasableSubset();
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "------------------------------" << std::endl
            << "Final Answer: UNSAT." << std::endl;
#endif
        return Answer::UNSAT;
      }
      else {
        // we would have returned SAT within the main loop,
        // so if after the main loop the problem is not UNSAT,
        // we simply don't know the answer
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "------------------------------" << std::endl
            << "Final Answer: UNKNOWN." << std::endl;
#endif
        return Answer::UNKNOWN;
      }
    }

  template<class Settings>
    ConstraintT ICPPDWModule<Settings>::deLinearize(const ConstraintT& c) {
      auto it = mDeLinearizations.find(c);
      if (it == mDeLinearizations.end()) {
        return c;
      }
      else {
        return it->second;
      }
    }

  template<class Settings>
    void ICPPDWModule<Settings>::createInfeasableSubset() {
      // the base set of conflicting constraints
      std::set<ConstraintT> conflictingConstraints = mSearchTree.getConflictingConstraints();

#ifdef PDW_MODULE_DEBUG_1
      std::cout << "Reasons: " << std::endl;
      for (const ConstraintT& c : conflictingConstraints) {
        std::cout << deLinearize(c) << ", ";
      }
#endif
      //now we have a set of conflicting constraints representing the infeasible set (TODO:minimal subset??)
      //store it in the variable "mInfeasibleSubsets"
      FormulaSetT infeasibleSubset; //a set of formulas which result in an UNSAT situation
      for (const ConstraintT& c : conflictingConstraints) {
        //get de-linearized constraints and their corresponding formulas, add them to the set
        //of infeasible constraints
        infeasibleSubset.insert(mConstraintFormula[deLinearize(c)]);
      }
      //if at least one constraint has been found, store it in the mInfeasibleSubset variables as inspected by
      //the governing algorithm
      if(!infeasibleSubset.empty()) {
        mInfeasibleSubsets.push_back(infeasibleSubset);
      }
    }

  template<class Settings>
    void ICPPDWModule<Settings>::setModel(Model model){
        mFoundModel = model;
    }

  template<class Settings>
    std::experimental::optional<Model> ICPPDWModule<Settings>::getSolution(ICPTree<Settings>* currentNode) {
      map<carl::Variable,double> sol(currentNode->getCurrentState().guessSolution());
      Model model;

#ifdef PDW_MODULE_DEBUG_1
        std::cout<< "Guessed solution:" << std::endl;
#endif
      for(auto& clause : sol) {
#ifdef PDW_MODULE_DEBUG_1
        std::cout << clause.first << ":" << clause.second << std::endl;
#endif
        Rational val = carl::rationalize<Rational>(clause.second);
        model.emplace(clause.first, val);
      }
      bool doesSat = true;
      for( const auto& rf : rReceivedFormula() ) {
        // TODO: This check is incomplete? Refer to ICPModule
        unsigned isSatisfied = carl::model::satisfiedBy(rf.formula().constraint(), model);
#ifdef PDW_MODULE_DEBUG_1
        std::cout << rf.formula().constraint() << "?" << isSatisfied << std::endl;
#endif
        assert(isSatisfied != 2);
        if(isSatisfied == 0 || isSatisfied == 2) {
          doesSat = false;
          break;
        }
      }

      if (doesSat) {
        return model;
      }
      else {
#ifdef SMTRAT_DEVOPTION_Statistics
          mStatistics.increaseNumberOfWrongGuesses();
#endif
        return std::experimental::optional<Model>();
      }
    }



}

#include "Instantiation.h"
