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
      mSearchTree(&mOriginalVariables,this),
      mOriginalVariables(),
      mActiveOriginalConstraints(),
      mContractionCandidates(),
      mActiveContractionCandidates(),
      mLinearizations(),
      mDeLinearizations(),
      mSlackVariables(),
      mMonomialSlackConstraints(),
      mMonomialSubstitutions()
      {
      }

  template<class Settings>
    ICPPDWModule<Settings>::~ICPPDWModule()
    {
    }

  template<class Settings>
    carl::Variable ICPPDWModule<Settings>::getSlackVariableForMonomial(Poly monomial) {
      // check if that monomial has been assigned to a slack variable already
      auto monomeSlackSubstitution = mMonomialSubstitutions.find(monomial);

      if (monomeSlackSubstitution != mMonomialSubstitutions.end()) {
        return monomeSlackSubstitution->second;
      }
      else {
        // introduce a new slack variable representing that monomial
        carl::Variable slackVariable = carl::freshRealVariable();
        mSlackVariables.insert(slackVariable);
        mMonomialSubstitutions[monomial] = slackVariable;

        // we create a new constraint (monomial - slack = 0) to connect the new slack variable with the monomial
        Poly slackPolynomial = monomial - slackVariable;
        ConstraintT slackConstraint(slackPolynomial, carl::Relation::EQ);
        mMonomialSlackConstraints.insert(slackConstraint);

        return slackVariable;
      }
    }

  template<class Settings>
    void ICPPDWModule<Settings>::linearizeConstraint(const ConstraintT& constraint) {
      const Poly& polynomial = constraint.lhs();

      // stores the original linearized constraint
      ConstraintT linearizedConstraint;

      if (polynomial.isLinear()) {
        // we don't need to do anything, so we simply map this constraint to itself
        linearizedConstraint = constraint;
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
          if (term.monomial() && !term.monomial()->isLinear()) {
            /*
             * Note: term == term.coeff() * term.monomial()
             */
            Poly monomial(term.monomial());

            // retrieve the slack variable for that monomial
            carl::Variable slackVariable = getSlackVariableForMonomial(monomial);

            // replace that monomial in the original constraint by the slack variable
            // polynomial = c_1 * m_1 + ... + c_n * m_n
            // replaced to: c_1 * slack + ...
            linearizedOriginalPolynomial += term.coeff() * carl::makePolynomial<Poly>(slackVariable);
          }
          else {
            linearizedOriginalPolynomial += term;
          }
        }

        // finally, we add the linearized original constraint
        linearizedConstraint = ConstraintT(linearizedOriginalPolynomial, constraint.relation());
      }

      // after we generated all constraints that will actually be used
      // we store the mapping of original constraint to linearized constraint
      mLinearizations[constraint] = linearizedConstraint;

      // and for convenience also a mapping of the linearized constraint to the original constraints
      // notice that we disregard slack substitutions here
      mDeLinearizations[linearizedConstraint] = constraint;
    }


  template<class Settings>
    void ICPPDWModule<Settings>::createAllContractionCandidates() {
      // create contraction candidates for "monomial - slack = 0"
      for (const ConstraintT& constraint : mMonomialSlackConstraints) {
        for (const auto& variable : constraint.variables()) {
          mContractionCandidates.push_back(ICPContractionCandidate<Settings>(variable, constraint));
        }
      }

      // create contraction candidates for "r_1 + ... + r_k ~ 0"
      for (const auto& it : mLinearizations) {
        const ConstraintT& constraint = it.second;
        // if the constraint only contains one variable, we cannot use it for contraction
        if (constraint.variables().size() > 1) {
          // we create a new contraction candidate for every variable in that constraint
          for (const auto& variable : constraint.variables()) {
            mContractionCandidates.push_back(ICPContractionCandidate<Settings>(variable, constraint));
          }
        }
      }
    }

  template<class Settings>
    bool ICPPDWModule<Settings>::informCore( const FormulaT& _constraint )
    {
      // we only consider actual constraints and ignore "!="-constraints (they will simply be checked in the end)
      if (_constraint.getType() == carl::FormulaType::CONSTRAINT && _constraint.constraint().relation() != carl::Relation::NEQ) {
        const ConstraintT& constraint = _constraint.constraint();

        //first add it to the map between constraints and formulas
        mConstraintFormula[constraint] = _constraint;

        // store all variables we see for book-keeping purposes
        for (const auto& var : constraint.variables()) {
          mOriginalVariables.insert(var);
        }

        // linearize the constraints
        linearizeConstraint(constraint);

#ifdef PDW_MODULE_DEBUG_1
        std::cout << "Linearized constraint for " << constraint << ":\n" << mLinearizations[constraint] << std::endl;
#endif
      }
      return true; // This should be adapted according to your implementation.
    }

  template<class Settings>
    void ICPPDWModule<Settings>::init()
    {
      // initialize all variables to unbounded
      mSearchTree.getCurrentState().initVariables(mOriginalVariables);
      mSearchTree.getCurrentState().initVariables(mSlackVariables);

      // generates all contraction candidates, i.e. for every constraint c
      // it generates a pair of (var, c) for every variable that occurs in that constraint
      createAllContractionCandidates();

      // also activate all contraction candidates for "monomial - slack = 0"
      for (const ConstraintT& constraint : mMonomialSlackConstraints) {
        for (auto& cc : mContractionCandidates) {
          if (cc.getConstraint() == constraint) {
            mActiveContractionCandidates.push_back(&cc);
          }
        }

        // and make the substitutions known to our search tree
        mSearchTree.addConstraint(constraint);
      }

#ifdef PDW_MODULE_DEBUG_1
      std::cout <<  "------------------------------------\nAll constraints informed.\n" << std::endl;
      std::cout << "Monomial-slack substitutions:" << endl;
      for (const ConstraintT& c : mMonomialSlackConstraints) {
        std::cout << c << endl;
      }
      std::cout << std::endl;

      std::cout << "Contraction Candidates:" << std::endl;
      for (const auto& cc : mContractionCandidates) {
        std::cout << cc << std::endl;
      }
      std::cout << std::endl;
#endif
    }

  template<class Settings>
    bool ICPPDWModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
      const FormulaT& formula = _subformula->formula();
      addReceivedSubformulaToPassedFormula(_subformula);

      // we only consider actual constraints
      bool causesConflict = false;
      if (formula.getType() == carl::FormulaType::CONSTRAINT && formula.constraint().relation() != carl::Relation::NEQ) {
        const ConstraintT& constraint = formula.constraint();
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "Adding core: " << constraint << std::endl;
#endif
        // A constraint was activated
        mActiveOriginalConstraints.insert(constraint);

        // we need to activate the contraction candidates for that constraint
        const ConstraintT& lC = mLinearizations[constraint];
        for (auto& cc : mContractionCandidates) {
          if (cc.getConstraint() == lC) {
            mActiveContractionCandidates.push_back(&cc);
          }
        }

        // we actually add the constraint to our search tree
        if(!mSearchTree.addConstraint(lC)) {
          causesConflict = true;
          createInfeasableSubset();
        }
      }

#ifdef PDW_MODULE_DEBUG_1
      if (causesConflict) {
        std::cout << "------------------------------" << std::endl
            << "Final Answer: UNSAT." << std::endl;
      }
#endif
      return !causesConflict;
    }

  template<class Settings>
    void ICPPDWModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
      const FormulaT& formula = _subformula->formula();

      // we only consider actual constraints
      if (formula.getType() == carl::FormulaType::CONSTRAINT && formula.constraint().relation() != carl::Relation::NEQ) {
        const ConstraintT& constraint = formula.constraint();

#ifdef PDW_MODULE_DEBUG_1
        std::cout <<  "Removing core: " << constraint << std::endl;
#endif
        // A constraint was de-activated
        auto cIt = std::find(mActiveOriginalConstraints.begin(), mActiveOriginalConstraints.end(), constraint);
        if (cIt != mActiveOriginalConstraints.end()) {
          mActiveOriginalConstraints.erase(cIt);
        }

        // we need to de-activate the contraction candidates for that constraint
        const ConstraintT& lC = mLinearizations[constraint];
        for (auto& cc : mContractionCandidates) {
          if (cc.getConstraint() == lC) {
            auto ccIt = std::find(mActiveContractionCandidates.begin(), mActiveContractionCandidates.end(), &cc);
            if (ccIt != mActiveContractionCandidates.end()) {
              mActiveContractionCandidates.erase(ccIt);
            }
          }
        }

        // we actually remove the constraint from within our search tree
        mSearchTree.removeConstraint(lC);
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

template<typename Settings>
class CompareTrees{
  public:
    bool operator()(ICPTree<Settings>* node1, ICPTree<Settings>* node2) {
    map<carl::Variable,double> sol(node1->getCurrentState().guessSolution());
    int numThis = 0;
    Model model;
    for(auto& clause : sol) {
      Rational val = carl::rationalize<Rational>(clause.second);
      model.emplace(clause.first, val);
    }
    for( const auto& rf : node1->getCorrespondingModule()->rReceivedFormula() ) {
      unsigned isSatisfied = carl::model::satisfiedBy(rf.formula().constraint(), model);
      assert(isSatisfied != 2);
      if(isSatisfied == 1) {
        numThis++;
      }
    }
    map<carl::Variable,double> sol2(node2->getCurrentState().guessSolution());
    int numThat = 0;
    Model model2;
    for(auto& clause : sol2) {
      Rational val = carl::rationalize<Rational>(clause.second);
      model2.emplace(clause.first, val);
    }
    for( const auto& rf : node1->getCorrespondingModule()->rReceivedFormula() ) {
      unsigned isSatisfied = carl::model::satisfiedBy(rf.formula().constraint(), model2);
      assert(isSatisfied != 2);
      if(isSatisfied == 1) {
        numThat++;
      }
    }
    return numThis<numThat;
    }
};


  template<class Settings>
    Answer ICPPDWModule<Settings>::checkCore(){
#ifdef SMTRAT_DEVOPTION_Statistics
    mStatistics.increaseNumberOfIterations();
#endif
#ifdef PDW_MODULE_DEBUG_1
      std::cout << "------------------------------------\n"
        << "Check core with the following active original constraints:" << std::endl;
      for (const auto& c : mActiveOriginalConstraints) {
        std::cout << c << std::endl;
      }
      std::cout << "\n" << std::endl;

      std::cout <<  "Check core with the following active contraction candidates:" << std::endl;
      for (ICPContractionCandidate<Settings>* cc : mActiveContractionCandidates) {
        std::cout << *cc << std::endl;
      }
      std::cout << std::endl;
#endif
      // clean up first
      // reset the found model for the next iteration
      mFoundModel = std::experimental::nullopt;

      // we need to search through all leaf nodes of the search tree, store them in a priority queue
      std::priority_queue<ICPTree<Settings>*,std::vector<ICPTree<Settings>*>,CompareTrees<Settings>> searchPriorityQueue;
      std::priority_queue<ICPContractionCandidate<Settings>*,std::vector<ICPContractionCandidate<Settings>*>,
             CompareCandidates<Settings>> ccPriorityQueue;

      mSearchTree.getCurrentState().initializeWeights(mActiveContractionCandidates);

      // add all candidates to the queue
      for (ICPContractionCandidate<Settings>* cc : mActiveContractionCandidates){
        ccPriorityQueue.push(cc);
      }


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
        bool splitOccurred = currentNode->contract(ccPriorityQueue,this);

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
              std::cout << "Consult the backend!" << std::endl;
#endif
              Answer answerByBackend = callBackend(currentNode);
              if(answerByBackend == Answer::SAT){
#ifdef PDW_MODULE_DEBUG_1
                std::cout << "The backend returned SAT." << std::endl;
#endif
                return Answer::SAT;
              }
              else if(answerByBackend == Answer::UNSAT){
#ifdef PDW_MODULE_DEBUG_1
                std::cout << "The backend returned UNSAT." << std::endl;
#endif
              }else{
#ifdef PDW_MODULE_DEBUG_1
                std::cout << "The backend returned UNKNOWN." << std::endl;
#endif
              }
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

      // conflicting constraints contains the raw unsat reason, i.e. all constraints and substitutions
      // we don't need slack substitutions, we need to de-linearize, and get the original formula
      FormulaSetT infeasibleSubset; //a set of formulas which result in an UNSAT situation
      for (const ConstraintT& c : conflictingConstraints) {
        // get de-linearized constraint
        ConstraintT d = deLinearize(c);

        // d can now either be an original constraint, or a slack substitution
        // we disregard slack substitutions, since they are irrelevant for unsat core
        auto formulaIt = mConstraintFormula.find(d);
        if (formulaIt != mConstraintFormula.end()) {
          infeasibleSubset.insert(formulaIt->second);
        }
      }

#ifdef PDW_MODULE_DEBUG_1
      std::cout << "Reasons: " << std::endl;
      for (const auto& i : infeasibleSubset) {
        std::cout << i.constraint() << std::endl;
      }
#endif

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
        std::cout << isSatisfied << " @ " << rf.formula().constraint() << std::endl;
#endif
        assert(isSatisfied != 2);
        if(isSatisfied == 0 || isSatisfied == 2) {
          doesSat = false;
          break;
        }
      }

      if (doesSat) {
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "All constraints satisfied.\n" << std::endl;
#endif
        return model;
      }
      else {
#ifdef PDW_MODULE_DEBUG_1
        std::cout << "Unsatisfied constraints remaining.\n" << std::endl;
#endif
#ifdef SMTRAT_DEVOPTION_Statistics
          mStatistics.increaseNumberOfWrongGuesses();
#endif
        return std::experimental::optional<Model>();
      }
    }

    template<class Settings>
    Answer ICPPDWModule<Settings>::callBackend(ICPTree<Settings>* currentNode){
      OneOrTwo<ConstraintT> tempConstr;
      std::vector<ModuleInput::iterator> tIteratorVector;
      for (const auto& var : mOriginalVariables) {
        IntervalT origInterval = currentNode->getCurrentState().getInterval(var);
        if (origInterval.isInfinite()) {
          continue;
        }
        tempConstr = ICPUtil<Settings>::intervalToConstraint(var, origInterval);
        //first create a formula out of the constraint, since the backend expects formulas
        FormulaT tFormula(tempConstr.first);
        //finally add the formula to the backend
        ModuleInput::iterator tIt = addSubformulaToPassedFormula(tFormula,tFormula).first;
        // store it to delete it later
        tIteratorVector.push_back(tIt);
        //check if we have an optional second part, and store it
        if(tempConstr.second){
          FormulaT tOptionalFormula((*tempConstr.second));
          //tempFormula.push_back(tOptionalFormula);
          tIt = addSubformulaToPassedFormula(tOptionalFormula,tOptionalFormula).first;
          tIteratorVector.push_back(tIt);
        }
      }
      Answer tempAnswer = runBackends();
      //model found, update it
      if(tempAnswer==Answer::SAT){
        //an update is not required since it is done in getBackendsModel()
        Module::getBackendsModel();
      }else if(tempAnswer==Answer::UNSAT){
        //otherwise get the infeasible subset

        // we cannot simply call getInfeasibleSubsets() because that method will try to
        // get the origins. but we don't really use origins and so it would lead to a segfault
        std::vector<FormulaSetT> backendInfSubsets;
        vector<Module*>::const_iterator backend = mUsedBackends.begin();
        while( backend != mUsedBackends.end() )
        {
            if( (*backend)->solverState() == UNSAT )
            {
                std::vector<FormulaSetT> infsubsets = (**backend).infeasibleSubsets();
                backendInfSubsets.insert(backendInfSubsets.end(), infsubsets.begin(), infsubsets.end() );
            }
            ++backend;
        }
        currentNode->setBackendsUnsat(backendInfSubsets);
      }
      //clean up after the backend has been consulted
      for(const auto& it: tIteratorVector){
        eraseSubformulaFromPassedFormula(it, true);
      }
      return tempAnswer;
    }


}

#include "Instantiation.h"
