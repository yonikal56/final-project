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
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/rational.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;

Node convertAssertion(TNode n, NodeMap& cache)
{
  for (TNode current :
       NodeDfsIterable(n, VisitOrder::POSTORDER, [&cache](TNode nn) {
         return cache.count(nn) > 0;
       }))
  {
    Node result;
    //std::cout<<toString(current.getKind())<<current.toString()<<to_string(current.getNumChildren())<<std::endl;
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();

    if (current.isVar() && current.getType() == nm->integerType())
    {
      result = sm->mkDummySkolem("__intToBag_var",
                                 nm->mkBagType(current.getType()),
                                 "Variable introduced in intToBag pass");
    }

    else if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else if (current.getNumChildren() == 2
             && (current.getKind() == Kind::MULT))
    {
      Assert(cache.find(current[0]) != cache.end());
      result = cache[current[0]];
      for (unsigned i = 1; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        Node child = current[i];
        Node childRes = cache[current[i]];
        //result = nm->mkNode(Kind::BAG_UNION_DISJOINT, result, childRes);
      }
    }
    else
    {
      NodeBuilder builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }

      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        builder << cache[current[i]];
      }
      result = builder;
    }
    cache[current] = result;
  }
  return cache[n];
}

Node convertIntToBag(int n)
{
  std::vector <Node> children;
  Node one = NodeManager::currentNM()->mkConstInt(Rational(1));
  Node two = NodeManager::currentNM()->mkConstInt(Rational(2));

  // Print the number of 2s that divide n
  while (n % 2 == 0) {
      Node node = NodeManager::currentNM()->mkNode(Kind::BAG_MAKE, two, one);
      children.push_back(node);
      n = n / 2;
  }

  // n must be odd at this point. So we can skip
  // one element (Note i = i +2)
  for (int i = 3; i <= std::sqrt(n); i = i + 2) {
      // While i divides n, print i and divide n
      while (n % i == 0) {
          Node num = NodeManager::currentNM()->mkConstInt(Rational(i));
          Node node = NodeManager::currentNM()->mkNode(Kind::BAG_MAKE, num, one);
          children.push_back(node);
          n = n / i;
      }
  }

  // This condition is to handle the case when n
  // is a prime number greater than 2
  if (n > 2)
  {
    Node num = NodeManager::currentNM()->mkConstInt(Rational(n));
    Node node = NodeManager::currentNM()->mkNode(Kind::BAG_MAKE, num, one);
    children.push_back(node);
  }

  if (children.size() == 1) {
    Node node = NodeManager::currentNM()->mkNode(Kind::BAG_MAKE, one, one);
    children.push_back(node);
  }

  Node result = children.at(0);
  int size = children.size();
  for (int i = 1; i < size; i++) {
    result = NodeManager::currentNM()->mkNode(Kind::BAG_UNION_DISJOINT, result, children.at(i));
  }

  return result;
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
  Trace("int-to-bags") << bag1 << bag2 << std::endl;
  Node res =
      NodeManager::currentNM()->mkNode(Kind::BAG_UNION_DISJOINT, bag1, bag2);

  NodeMap cache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, convertAssertion((*assertionsToPreprocess)[i], cache));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
