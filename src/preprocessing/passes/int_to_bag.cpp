/******************************************************************************
* Top contributors (to current version):
*   Ying Sheng, Yoni Zohar, Aina Niemetz
*
* This file is part of the cvc5 project.
*
* Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
* in the top-level source directory and their institutional affiliations.
* All rights reserved.  See the file COPYING in the top-level source
* directory for licensing information.
* ****************************************************************************
*
* Ackermannization preprocessing pass.
*
* This implements the Ackermannization preprocessing pass, which enables
* very limited theory combination support for eager bit-blasting via
* Ackermannization. It reduces constraints over the combination of the
* theories of fixed-size bit-vectors and uninterpreted functions as
* described in
*   Liana Hadarean, An Efficient and Trustworthy Theory Solver for
*   Bit-vectors in Satisfiability Modulo Theories.
*   https://cs.nyu.edu/media/publications/hadarean_liana.pdf
*/

#include "preprocessing/passes/int_to_bag.h"

#include <cmath>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "smt/logic_exception.h"
#include "options/base_options.h"
#include "options/options.h"
#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/rational.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Node convertIntToBag(int n) {
    std::vector<Node> children;

    // Print the number of 2s that divide n
    while (n % 2 == 0)
    {
      children.push_back(NodeManager::currentNM()->mkConstInt(Rational(2)));
      n = n/2;
    }

    // n must be odd at this point. So we can skip
    // one element (Note i = i +2)
    for (int i = 3; i <= std::sqrt(n); i = i + 2)
    {
      // While i divides n, print i and divide n
      while (n % i == 0)
      {
        children.push_back(NodeManager::currentNM()->mkConstInt(Rational(i)));
        n = n/i;
      }
    }

    // This condition is to handle the case when n
    // is a prime number greater than 2
    if (n > 2)
      children.push_back(NodeManager::currentNM()->mkConstInt(Rational(n)));

  Node node = NodeManager::currentNM()->mkNode(Kind::SET_INSERT, children.at(1));
  int size = children.size();
  for (int j = 1; j < size; j++) {
    node = NodeManager::currentNM()->mkNode(Kind::SET_INSERT, node, children.at(j));
  }


    return node;
}

IntToBag::IntToBag(PreprocessingPassContext* preprocContext)
   : PreprocessingPass(preprocContext, "int-to-bag"),
     d_funcToSkolem(userContext()),
     d_usVarsToBVVars(userContext()),
     d_logic(logicInfo())
{
}

PreprocessingPassResult IntToBag::applyInternal(
   AssertionPipeline* assertionsToPreprocess)
{
  Node bag1 = convertIntToBag(315);
  Node bag2 = convertIntToBag(19);
  Node res = NodeManager::currentNM()->mkNode(Kind::BAG_UNION_DISJOINT, bag1, bag2);

  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
 {
   assertionsToPreprocess->replace(
       i, rewrite(res));
 }

 return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
