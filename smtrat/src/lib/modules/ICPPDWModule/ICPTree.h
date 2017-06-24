/*
 * File:   ICPTree.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "ICPState.h"
#include "ICPPDWComperators.h"

namespace smtrat
{
  template<typename Settings>
  class ICPPDWModule;
  /**
   * Represents the ICP search tree.
   */
  template<typename Settings>
  class ICPTree
  {
    private:
      /**in order to find out when to terminate we need to check if the diameter has
       * been reached. for this purpose a pointer to the initial set of variables is required
       */
      std::set<carl::Variable>* mOriginalVariables;

      // the current ICP state.
      ICPState<Settings> mCurrentState;

      // the parent ICP state
      std::experimental::optional<ICPTree<Settings>*> mParentTree;

      // the child states
      unique_ptr<ICPTree<Settings>> mLeftChild;
      unique_ptr<ICPTree<Settings>> mRightChild;

      // dimension in which the split occurred, if a split occurred
      std::experimental::optional<carl::Variable> mSplitDimension;

      // In case of UNSAT, this set will contain the reason for unsatisfiability.
      std::set<ConstraintT> mConflictingConstraints;

      // In case of UNSAT, this set will contain the variables that were involved in the unsat core
      std::set<carl::Variable> mConflictingVariables;

      // Stores whether this state has been determined to be unsat
      bool mIsUnsat;

      // stores all simple bounds that have been used to initialize the variable bounds
      std::set<ConstraintT> mActiveSimpleBounds;

      //
      ICPPDWModule<Settings>* mModule;

    public:
      ICPTree(std::set<carl::Variable>* originalVariables,ICPPDWModule<Settings>* module);
      ICPTree(ICPTree<Settings>* parent, const ICPState<Settings>& parentState, std::set<carl::Variable>* originalVariables, const std::set<ConstraintT>& simpleBounds,ICPPDWModule<Settings>* module);

      /**
       * Contracts the current ICP state until either:
       * 1) A split occurs.
       *    In this case, two new child trees which correspond to the split search space
       *    will be added to mChildTrees, and true will be returned.
       * 2) The bounds are UNSAT.
       *    In this case, the current ICP state will contain a set of conflicting constraints,
       *    and - since no split occurred - false will be returned.
       * 3) Some other termination criterium was met.
       *    (E.g. the target diameter for all intervals was reached)
       *    In this case, no child trees will be added, and no conflicting constraints will
       *    be determined. Since no split occurred, false will be returned.
       *
       * A method caller can determine which of these cases happened through the return value
       * of this method and the isUnsat method of the current ICP state.
       *
       * @param contractionCandidates A set of pointers to contraction candidates that can be applied
       * @return whether a split occurred
       */
      bool contract(std::priority_queue<ICPContractionCandidate<Settings>*,std::vector<ICPContractionCandidate<Settings>*>,
             CompareCandidates<Settings>>& ccPriorityQueue,ICPPDWModule<Settings>* module);

      ICPState<Settings>& getCurrentState();

      std::experimental::optional<ICPTree<Settings>*> getParentTree();

      ICPTree<Settings>* getLeftChild();

      ICPTree<Settings>* getRightChild();

      bool isLeaf();

      /**
       * @return a list of leaf nodes of this search tree
       */
      vector<ICPTree<Settings>*> getLeafNodes();

      std::experimental::optional<carl::Variable> getSplitDimension();

      std::set<ConstraintT>& getConflictingConstraints();

      std::set<carl::Variable>& getConflictingVariables();

      /**
       * @return whether the search on this tree has led to an empty interval
       */
      bool isUnsat();

      /**
       * After a backend determined that this node is unsat, we have to set the conflicting
       * constraints according to the backends' infeasible subsets.
       * @param the infeasible subsets of the backends
       */
      void setBackendsUnsat(std::vector<FormulaSetT>& backendInfSubsets);

      /**
       * Logs all current variable bounds.
       */
      void printVariableBounds();

      /**
       * @return the number of splits that occurred
       */
      int getNumberOfSplits();

      /**
       * Informs the current variable bounds about a new constraint.
       * The variable bounds will then be re-calculated to include that new constraint.
       *
       * @param _constraint The new constraint
       * @param _origin The formula where the constraint originates from
       * @return false if the new constraint immediatly caused conflicting bounds
       */
      bool addConstraint(const ConstraintT& _constraint);

      /**
       * Removes a constraint from the current search tree.
       * The variable bounds and tree structure will then be re-calculated to exclude that new constraint.
       *
       * @param _constraint The new constraint
       * @param _origin The formula where the constraint originates from
       */
      void removeConstraint(const ConstraintT& _constraint);

      ICPPDWModule<Settings>* getCorrespondingModule();

      static bool compareTrees(ICPTree<Settings>* node1, ICPTree<Settings>* node2);


    private:
      void removeConstraint(const ConstraintT& _constraint, std::set<carl::Variable> involvedVars, std::set<ConstraintT> involvedConstraints);

      /**
       * Does all necessary steps if a state has been determined to be unsat.
       * I.e., it will generate conflict reasons, set appropriate member variables etc.
       */
      void handleUnsat();

      /**
       * Resets the tree to a state where no unsat has been determined yet,
       * i.e. conflicting variables and constraints will be cleared and mUnsat will be set to false.
       */
      void clearUnsat();

      /**
       * Splits the search tree.
       * @param var the split dimension
       */
      void split(carl::Variable var);

      /**
       * Retrieves and stores the reasons why the current state is UNSAT.
       * I.e. retrieves the constraints that were used to contract the
       * conflicting variables to an empty interval. And stores them in mConflictingConstraints.
       */
      void generateConflictReasons();

      /**
       * Accumulates all conflict reasons of the children as its own conflict reasons.
       * But only if all child trees are indeed unsat.
       * If at least one of the children is not unsat, this method does nothing.
       */
      void accumulateConflictReasons();

      /**
       * Returns the root of the overall tree. Required for counting number of splits.
       */
      ICPTree<Settings>* getRoot();

      /**
       * Traverses the tree and retrieves the number of performed splits.
       */
      int getNumberOfSplitsRecursive();
  };
}
