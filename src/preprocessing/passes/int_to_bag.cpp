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


Node IntToBag::convertAssertion(TNode n, NodeMap& cache, vector<Node>& vars)
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
      //result = nm->mkNode(Kind::GEQ, nm->mkNode(Kind::BAG_TO_INT, cache[current[0]]), current[1]);
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
      Node definition = nm->mkNode(Kind::BAG_TO_INT, result);
      d_preprocContext->addSubstitution(current, definition);
    }
    else if (current.isConst() && current.getType() == nm->integerType())
    {
      result = nm->mkNode(Kind::INT_TO_BAG, current);//convertIntToBag(current.getConst<Rational>().getNumerator().getSigned64());
    }

    else if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else if ((current.getKind() == Kind::NONLINEAR_MULT) || (current.getKind() == Kind::MULT))
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
    else if (current.getKind() == Kind::ADD || current.getKind() == Kind::SUB)
    {
      result = nm->mkNode(Kind::INT_TO_BAG ,nm->mkNode(current.getKind(), nm->mkNode(Kind::BAG_TO_INT, cache[current[0]]), nm->mkNode(Kind::BAG_TO_INT, cache[current[1]])));
    }
    else
    {
      Assert(false) << "Got kind: " << current.getKind() << "\nCurrent:" << current << std::endl;
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
