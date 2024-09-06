Original CVC5 README file: https://github.com/cvc5/cvc5/blob/main/README.md

cvc5
===============================================================================

cvc5 is a tool for determining the satisfiability of a first order formula
modulo a first order theory (or a combination of such theories).  It is the
fifth in the Cooperating Validity Checker family of tools (CVC, CVC Lite,
CVC3, CVC4) but does not directly incorporate code from any previous version
prior to CVC4.


The idea of this project
-------------------------------------------------------------------------------

This project exapnds cvc5 and adds the "--solve-int-as-bag" option.
This options runs a preprocessing pass that changes any assertion to be made of bags (multi-sets) instead of integers. Therefore, multiplication becomes the union disjoint of bags instead of multiplication of integers.
The equivilant bag of an integer will be the prime factorization of the integer.
Since we deal only with positive integers (only natural integers have a unique prime factorization), we map the Integers to the Natural numbers. For example - the bag (0 2) will represent the number 2^2=4.

In addition, we implemented other operators based on this idea - gcd, lsm, is.prime, num.of.factors factors.


Results of tests
-------------------------------------------------------------------------------

We compared the results of cvc5 with and without our preprocssing pass.
All the tests included multiplication or the new operators. For the new operators, we wrote an equivilant tests without those operators, since cvc5 does not know how to solve them without our option.
The operators free versions inclueds quantifiers, so while running them, the "--cegqi-all --nl-ext-tplanes" flags should be added.

All the tests can be found in the "evaluation" folder which has 3 subfolders:
- "multiplication" folder which has different kinds of multiplication tests
- "operators" folder which has tests for the oprators in both forms - "original" (using our option) and "primitive" (pure cvc5)
- "randomTests" folder which has random tests that includes only multiplication, but create randomly.
Each folder includes the appropriate python files that generated the tests and a bash scripts that compare the results for only those tests.

We finally run the tests on a large cluster, a detailed comparison of the results can be found in the "tests_results_on_cluster.txt" file.
The results show a great advantage to our preprocessing path for both the multiplication tests and the operators tests.


This files (with respect to cvc5 original branch)
-------------------------------------------------------------------------------

As described, the "evaluation" folder includes all the tests and the "tests_results_on_cluster.txt" file includes the results of the tests on our cluster.
The src/preprocessing/passes/int_to_bag.cpp has the actual preprocessing pass code.
The src/theory/bags/bags_utils.cpp was changed to include the mapping from Integers to Natural numbers (and the inverse mapping), and an implementation of bag.to.int and int.to.bag operators (converts bag to integer based on our prime factorization reprsentation and inverse conversion respectivley).
The other operators are only implemented in our preprocessing pass, but the kinds was added to all the needed files (multiple files with a small change in each).


Authors
-------------------------------------------------------------------------------

Any change in this fork was written by Yehonatan Calinsky and Yoni Zohar.
