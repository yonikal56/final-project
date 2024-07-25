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
 * Int to bag preprocessing pass.
 *
 */

#include "preprocessing/passes/int_to_bag.h"

#include <cmath>
#include <vector>
#include <algorithm>

#include "base/check.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/emptybag.h"
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

void addToMap(std::map<int, int> &map, int newNum) {
  if(map.find(newNum) == map.end()){
    map[newNum] = 1;
  }else{
    map[newNum] += 1;
  }
}

Node convertIntToBag(int n)
{
  Assert(n != 0);
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> children;
  std::map<int, int> nums;
  Node emptyPart = nm->mkConst(EmptyBag(nm->mkBagType(nm->integerType())));

  if (n == 1)
  {
    return emptyPart;
  }

  // Print the number of 2s that divide n
  while (n % 2 == 0)
  {
    addToMap(nums, 2);
    n = n / 2;
  }

  // n must be odd at this point. So we can skip
  // one element (Note i = i +2)
  for (int i = 3; i <= std::sqrt(n); i = i + 2)
  {
    // While i divides n, print i and divide n
    while (n % i == 0)
    {
      addToMap(nums, i);
      n = n / i;
    }
  }

  // This condition is to handle the case when n
  // is a prime number greater than 2
  if (n > 2)
  {
    addToMap(nums, n);
  }

  for (auto i = nums.begin(); i != nums.end(); ++i) {
    Node first = NodeManager::currentNM()->mkConstInt(Rational(i->first));
    Node second = NodeManager::currentNM()->mkConstInt(Rational(i->second));
    Node node = NodeManager::currentNM()->mkNode(Kind::BAG_MAKE, first, second);
    children.push_back(node);
  }

  if (children.size() == 0)
  {
    return emptyPart;
  }

  if (children.size() == 1)
  {
    return children.at(0);
  }

  Node result = children.at(0);
  int size = children.size();
  for (int i = 1; i < size; i++)
  {
    result = NodeManager::currentNM()->mkNode(
        Kind::BAG_UNION_DISJOINT, result, children.at(i));
  }

  return result;
}

Node convertAssertion(TNode n, NodeMap& cache, vector<Node>& vars)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();


  for (TNode current :
       NodeDfsIterable(n, VisitOrder::POSTORDER, [&cache](TNode nn) {
         return cache.count(nn) > 0;
       }))
  {
    Node result;
    Trace("int-to-bags") << toString(current.getKind()) << "," << current.toString() << ","
                         << to_string(current.getNumChildren()) << std::endl;

    if (current.getKind() == Kind::GEQ)
    {
      vars.erase(remove(vars.begin(), vars.end(), current[0]), vars.end());
      Assert(current[1].getConst<Rational>().getNumerator() == 1);
      result = nm->mkConst(true);
    }
    else if (current.getKind() == Kind::PRIME)
    {
      Node card = nm->mkNode(Kind::BAG_CARD, cache[current[0]]);
      result = nm->mkNode(Kind::EQUAL, card, nm->mkConstInt(Rational(1)));
    }
    else if (current.getKind() == Kind::FACTORS)
    {
      result = nm->mkNode(Kind::BAG_SETOF, cache[current[0]]);
    }
    else if (current.getKind() == Kind::NUMOFFACTORS)
    {
      result = nm->mkNode(Kind::BAG_CARD, nm->mkNode(Kind::BAG_SETOF, cache[current[0]]));
    }
    else if (current.getKind() == Kind::GCD)
    {
      result = nm->mkNode(Kind::BAG_INTER_MIN, cache[current[0]], cache[current[1]]);
    }
    else if (current.getKind() == Kind::LCM)
    {
      result = nm->mkNode(Kind::BAG_UNION_MAX, cache[current[0]], cache[current[1]]);
    }
    else if (current.isVar() && current.getType() == nm->integerType())
    {
      vars.push_back(current);
      result = sm->mkDummySkolem("__intToBag_var",
                                 nm->mkBagType(current.getType()),
                                 "Variable introduced in intToBag pass");
    }
    else if (current.isConst() && current.getType() == nm->integerType())
    {
      result = convertIntToBag(current.getConst<Rational>().getNumerator().getSignedInt());
    }

    else if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else if ((current.getKind() == Kind::NONLINEAR_MULT))
    {
      Assert(cache.find(current[0]) != cache.end());
      result = cache[current[0]];
      for (unsigned i = 1; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        Node child = current[i];
        Node childRes = cache[current[i]];
        result = nm->mkNode(Kind::BAG_UNION_DISJOINT, result, childRes);
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
  NodeManager::currentNM()->mkConstInt(Rational(2));
  NodeMap cache;
  vector<Node> vars;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, convertAssertion((*assertionsToPreprocess)[i], cache, vars));
  }
  if (!vars.empty())
  {
    throw LogicException("Int to bag require all variables to be >= 1");
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
