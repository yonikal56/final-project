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

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

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

 /* replace applications of UF by skolems */
 // FIXME for model building, github issue #1901
 for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
 {
   Node result = Node();
   assertionsToPreprocess->replace(
       i, result);
 }

 return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
