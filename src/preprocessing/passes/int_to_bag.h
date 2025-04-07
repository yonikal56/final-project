/******************************************************************************
 * Top contributors (to current version):
 *   Yehonatan Calinsky, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Int to bag preprocessing pass.
 *
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__INT_TO_BAG_H
#define CVC5__PREPROCESSING__PASSES__INT_TO_BAG_H

#include <unordered_map>

#include <vector>
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {
using NodeMap = std::unordered_map<Node, Node>;
using TNodeSet = std::unordered_set<TNode>;
using FunctionToArgsMap = std::unordered_map<TNode, TNodeSet>;
using USortToBVSizeMap = std::unordered_map<TypeNode, size_t>;

class IntToBag : public PreprocessingPass
{
 public:
  IntToBag(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  void addFinalizeAssertions(AssertionPipeline* assertionsToPreprocess,
                             const std::vector<Node>& additionalConstraints);

 private:
  /* Map each function to a set of terms associated with it */
  FunctionToArgsMap d_funcToArgs;
  /* Map each function-application term to the new Skolem variable created by
   * ackermannization */
  theory::SubstitutionMap d_funcToSkolem;
  /* Map each variable with uninterpreted sort to the new Skolem BV variable
   * created by ackermannization */
  theory::SubstitutionMap d_usVarsToBVVars;
  /* Map each uninterpreted sort to the number of variables in this sort. */
  USortToBVSizeMap d_usortCardinality;
  /* Convert old assertions to new versions */
  /*
   * Any integer is converted to a bag of the following form:
   * - empty bag represents the number 0
   * - if 0 appears once in the bag, the number is negative. 0 can not appear more than once in a bag
   * - for any non-zero number, 1 appears exactly once in the bag
   * - every number except for 0 and 1, is converted to a positive number
   * (using the theory/bags/bags_utils.cppt/intFactorizationPositiveToZ function), representing a prime factor
   */
  Node convertAssertion(TNode n, NodeMap& cache, std::vector<Node>& vars, std::vector<Node>& additionalConstraints);
  LogicInfo d_logic;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__INT_TO_BAG_H */
