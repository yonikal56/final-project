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
#include "theory/bags/bags_utils.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;


Node IntToBag::convertAssertion(TNode n, NodeMap& cache, vector<Node>& vars, vector<Node>& additionalConstraints)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  Node bagZero = nm->mkNode(Kind::BAG_MAKE, zero, one);
  Node bagOne = nm->mkNode(Kind::BAG_MAKE, one, one);
  Node bagOneZero = nm->mkNode(Kind::BAG_UNION_DISJOINT, bagZero, bagOne);
  Node emptyPart = nm->mkConst(EmptyBag(nm->mkBagType(nm->integerType())));

  for (TNode current :
       NodeDfsIterable(n, VisitOrder::POSTORDER, [&cache](TNode nn) {
         return cache.count(nn) > 0;
       }))
  {
    Node result;
    Trace("int-to-bags") << toString(current.getKind()) << "," << current.toString() << ","
                         << to_string(current.getNumChildren()) << std::endl;

    if (current.getKind() == Kind::PRIME)
    {
      // if empty or negative, false. Else, cardinality of bag without 1
      Node emptyCond = nm->mkNode(Kind::EQUAL, cache[current[0]], emptyPart);
      emptyCond = nm->mkNode(Kind::OR, emptyCond,
                                    nm->mkNode(Kind::BAG_MEMBER, zero, cache[current[0]]));
      Node card = nm->mkNode(Kind::BAG_CARD, nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[0]], bagOne));
      result = nm->mkNode(Kind::ITE, emptyCond, nm->mkConst(false), nm->mkNode(Kind::EQUAL, card, nm->mkConstInt(Rational(1))));
    }
    else if (current.getKind() == Kind::SAME_FACTORS)
    {
      // remove 1 and 0
      result = nm->mkNode(Kind::EQUAL,
                          nm->mkNode(Kind::BAG_SETOF, nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[0]], bagOneZero)),
                          nm->mkNode(Kind::BAG_SETOF, nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[1]], bagOneZero)));
    }
    else if (current.getKind() == Kind::NUMOFFACTORS)
    {
      // remove 1 and 0
      result = nm->mkNode(Kind::BAG_CARD, nm->mkNode(Kind::BAG_SETOF, nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[0]], bagOneZero)));
    }
    else if (current.getKind() == Kind::GCD)
    {
      // we fixed GCD(0,0)=0
      // remove 1 and 0 and add 1 in the end
      Node emptyCond = nm->mkNode(Kind::EQUAL, cache[current[0]], emptyPart);
      Node emptyOr = nm->mkNode(Kind::AND, emptyCond, nm->mkNode(Kind::EQUAL, cache[current[1]], emptyPart));
      Node oneWithout = nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[0]], bagOneZero);
      Node twoWithout = nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[1]], bagOneZero);
      result = nm->mkNode(Kind::ITE, emptyOr, emptyPart,
                              nm->mkNode(Kind::BAG_UNION_DISJOINT,  nm->mkNode(Kind::BAG_INTER_MIN, oneWithout, twoWithout), bagOne));
    }
    else if (current.getKind() == Kind::LCM)
    {
      // we fixed LCM(0,a)=0
      // remove 1 and 0 and add 1 in the end
      Node emptyCond = nm->mkNode(Kind::EQUAL, cache[current[0]], emptyPart);
      Node emptyOr = nm->mkNode(Kind::OR, emptyCond, nm->mkNode(Kind::EQUAL, cache[current[1]], emptyPart));
      Node oneWithout = nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[0]], bagOneZero);
      Node twoWithout = nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, cache[current[1]], bagOneZero);
      result = nm->mkNode(Kind::ITE, emptyOr, emptyPart,
                          nm->mkNode(Kind::BAG_UNION_DISJOINT,  nm->mkNode(Kind::BAG_UNION_MAX, oneWithout, twoWithout), bagOne));
    }
    else if (current.isVar() && current.getType() == nm->integerType())
    {
      result = sm->mkDummySkolem("__intToBag_var",
                                 nm->mkBagType(current.getType()),
                                 "Variable introduced in multiplication pass");
      Node definition = nm->mkNode(Kind::BAG_TO_INT, result);
      d_preprocContext->addSubstitution(current, definition);
      additionalConstraints.push_back(nm->mkNode(Kind::LEQ, nm->mkNode(Kind::BAG_COUNT, zero, result), one));
      additionalConstraints.push_back(nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::BAG_COUNT, one, result), one));
    }
    else if (current.isConst() && current.getType() == nm->integerType())
    {
      result = nm->mkNode(Kind::INT_TO_BAG, current);
    }

    else if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else if ((current.getKind() == Kind::NONLINEAR_MULT) || (current.getKind() == Kind::MULT))
    {
      Assert(cache.find(current[0]) != cache.end());
      result = cache[current[0]];
      Node emptyOr = nm->mkNode(Kind::EQUAL, result, emptyPart);
      Node xorPart = nm->mkNode(Kind::BAG_MEMBER, zero, result);
      Node unionDisjointPart = result;
//      Node unionDisjointPart = nm->mkNode(Kind::BAG_UNION_DISJOINT,
//                                          bagOne,
//                                          nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, result, bagOneZero));
      for (unsigned i = 1; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        Node child = current[i];
        Node childRes = cache[current[i]];
        //result = nm->mkNode(Kind::BAG_UNION_DISJOINT, result, childRes);
        emptyOr = nm->mkNode(Kind::OR, emptyOr, nm->mkNode(Kind::EQUAL, childRes, emptyPart));
        xorPart = nm->mkNode(Kind::XOR, xorPart, nm->mkNode(Kind::BAG_MEMBER, zero, childRes));
        unionDisjointPart = nm->mkNode(Kind::BAG_UNION_DISJOINT, unionDisjointPart, childRes);
        //unionDisjointPart = nm->mkNode(Kind::BAG_UNION_DISJOINT, unionDisjointPart, nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, childRes, bagOneZero));
      }
      Node xorITE = nm->mkNode(Kind::ITE, xorPart, bagZero, emptyPart);
      unionDisjointPart = nm->mkNode(Kind::BAG_UNION_DISJOINT, nm->mkNode(Kind::BAG_DIFFERENCE_REMOVE, unionDisjointPart, bagOneZero), bagOne);
      result = nm->mkNode(Kind::ITE, emptyOr, emptyPart,
                          nm->mkNode(Kind::BAG_UNION_DISJOINT,
                                     unionDisjointPart,
                                     xorITE));
      // result = (ite (x bag empty or y bag empty) (bag empty) ((((x/{0,1})ud(y/{0,1}))ud({1 1}))(bag.empty))ud(ite (0 in x xor 0 in y) ({0 1}) (bag empty)))))
    }
    else if (current.getKind() == Kind::EQUAL || current.getKind() == Kind::NOT || current.getKind() == Kind::AND
             || current.getKind() == Kind::OR || current.getKind() == Kind::IMPLIES || current.getKind() == Kind::BOUND_VAR_LIST || current.getKind() == Kind::FORALL)
    {
      NodeBuilder builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }

      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        if (cache[current[i]].getKind() == Kind::DUMMY_SKOLEM || cache[current[i]].getType().isBag())
        {
          builder << cache[current[i]];
        }
        else
        {
          builder << cache[current[i]];
        }
      }
      result = builder;
    }
    else if (current.getType().isBag()) {
      result = current;
    }
    else if (current.getKind() == Kind::ADD || current.getKind() == Kind::SUB)
    {
      result = nm->mkNode(Kind::INT_TO_BAG,
                          nm->mkNode(current.getKind(),
                                     nm->mkNode(Kind::BAG_TO_INT, cache[current[0]]),
                                     nm->mkNode(Kind::BAG_TO_INT, cache[current[1]])));
    }
    else if (current.getKind() == Kind::GEQ || current.getKind() == Kind::GT || current.getKind() == Kind::LEQ || current.getKind() == Kind::LT)
    {
      Trace("int-to-bags") << "kind is:"
                           << current.getKind() << std::endl;
      result = nm->mkNode(current.getKind(),
               nm->mkNode(Kind::BAG_TO_INT, cache[current[0]]),
               nm->mkNode(Kind::BAG_TO_INT, cache[current[1]]));
    }
    else
    {
      Assert(false) << "Got kind: " << current.getKind() << "\nType:" << current.getType() << "\nCurrent:" << current << std::endl;
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
  std::vector<Node> additionalConstraints;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, convertAssertion((*assertionsToPreprocess)[i], cache, vars,
                            additionalConstraints));
  }
  if (!vars.empty())
  {
    throw LogicException("Int to bag require all variables to be >= 1");
  }

  addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);

  return PreprocessingPassResult::NO_CONFLICT;
}

void IntToBag::addFinalizeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    const std::vector<Node>& additionalConstraints)
{
  NodeManager* nm = nodeManager();
  Node lemmas = nm->mkAnd(additionalConstraints);
  assertionsToPreprocess->push_back(lemmas);
  Trace("bv-to-int-debug") << "range constraints: " << lemmas.toString()
                           << std::endl;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
