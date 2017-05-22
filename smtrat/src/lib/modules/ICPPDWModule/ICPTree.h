/*
 * File:   ICPTree.h
 * Author: David
 */

#pragma once

#include "../../Common.h"
#include "ICPState.h"

namespace smtrat
{
  /**
   * Represents the ICP search tree.
   */
  class ICPTree
  {
    private:
      /**in order to find out when to terminate we need to check if the diameter has
       * been reached. for this purpose a pointer to the initial set of variables is required
       */
      std::set<carl::Variable>* mOriginalVariables;

      // the current ICP state.
      ICPState mCurrentState;

      // the parent ICP state
      std::experimental::optional<ICPTree*> mParentTree;

      // the child states
      unique_ptr<ICPTree> mLeftChild;
      unique_ptr<ICPTree> mRightChild;

      // dimension in which the split occurred, if a split occured
      std::experimental::optional<carl::Variable> mSplitDimension;

      // In case of UNSAT, this set will contain the reason for unsatisifiabilty.
      std::set<ConstraintT> mConflictingConstraints;

    public:
      ICPTree();
      ICPTree(std::set<carl::Variable>* originalVariables);
      ICPTree(ICPTree* parent, const vb::VariableBounds<ConstraintT>& parentBounds,std::set<carl::Variable>* originalVariables);

      /**
       * Contracts the current ICP state until either:
       * 1) A split occurrs.
       *    In this case, two new child trees which correspond to the splitted search space
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
      bool contract(vector<ICPContractionCandidate*>& contractionCandidates);

      ICPState& getCurrentState();

      std::experimental::optional<ICPTree*> getParentTree();

      ICPTree* getLeftChild();

      ICPTree* getRightChild();

      bool isLeaf();

      /**
       * @return a list of leaf nodes of this search tree
       */
      vector<ICPTree*> getLeafNodes();

      std::experimental::optional<carl::Variable> getSplitDimension();

      std::set<ConstraintT>& getConflictingConstraints();

      /**
       * @return whether the search on this tree has led to an empty interval
       */
      bool isUnsat();

      /**
       * Logs all current variable bounds.
       */
      void printVariableBounds();

      int getNumberOfSplits();

    private:
      /**
       * Splits the search tree.
       * @param var the split dimension
       */
      void split(carl::Variable var);

      /**
       * Retrieves the reasons why the current state is UNSAT.
       * I.e. retrieves the constraints that were used to contract the
       * given variable to an empty interval.
       *
       * @param conflictVar the variable that has been contracted to an empty interval
       * @return a list of conflict reasons (original constraints)
       */
      std::set<ConstraintT> getConflictReasons(carl::Variable conflictVar);

      /**
       * Accumulates all conflict reasons of the children as its own conflict reasons.
       * But only if all child trees are indeed unsat.
       * If at least one of the children is not unsat, this method does nothing.
       */
      void accumulateConflictReasons();
      /**
       * Returns the root of the overall tree. Required for counting number of splits.
       */
      ICPTree* getRoot();
      /**
       * Traverses the tree and retrieves the number of performed splits.
       */
      int getNumberOfSplitsRecursive();

  };
}
