Original CVC5 README file: https://github.com/cvc5/cvc5/blob/main/README.md

cvc5
===============================================================================

cvc5 is a tool for determining the satisfiability of a first order formula
modulo a first order theory (or a combination of such theories).  It is the
fifth in the Cooperating Validity Checker family of tools (CVC, CVC Lite,
CVC3, CVC4) but does not directly incorporate code from any previous version
prior to CVC4.


Project Overview
-------------------------------------------------------------------------------

This project expands CVC5 by adding the **--solve-int-as-bag** option. This option introduces a preprocessing pass that transforms any assertions involving integers into assertions involving bags (multi-sets). As a result, multiplication is interpreted as the union disjoint of bags instead of the multiplication of integers. The equivalent bag representation of an integer is based on its prime factorization. Since this approach only deals with positive integers (which have unique prime factorizations), integers are mapped to natural numbers. For example, the bag (0, 2) represents the number 2^2=4.

In addition to this transformation, new operators have been implemented based on this idea:
1. gcd (greatest common divisor)
2. lcm (least common multiple)
3. is_prime (checks if a number is prime)
4. num_of_factors (counts the number of different prime factors of a number)
5. factors (lists the prime factors of a number)


Test Results
-------------------------------------------------------------------------------

We compared the results of CVC5 with and without our preprocessing pass. All tests included either multiplication or the new operators. For the new operators, we created equivalent tests without using those operators since CVC5 does not natively support them without our option. The versions without these operators include quantifiers, so when running them, the **--cegqi-all --nl-ext-tplanes** flags should be used.

All tests are organized into the following subfolders within the "evaluation" folder:
1. multiplication: Contains various tests involving multiplication.
2. operators: Contains tests for the new operators in two forms:
   - original: Using the new operators.
   - primitive: Using pure CVC5 logic without the new operators.
3. randomTests: Contains randomly generated tests that involve only multiplication.
Each folder includes Python scripts for generating tests and Bash scripts for comparing the results.

Tests were executed on a large cluster, and a detailed comparison of the results can be found in the "tests_results_on_cluster.txt" file.
The results indicate a significant performance advantage for our preprocessing pass in both multiplication and operator tests.


Modified Files (Relative to the Original CVC5 Branch)
-------------------------------------------------------------------------------

1. Evaluation folder: Contains all test cases and results.
2. src/preprocessing/passes/int_to_bag.cpp(h): Contains the code for the new preprocessing pass and the new operators conversion to bag operators.
3. src/theory/bags/bags_utils.cpp(h): Modified to include the mapping between integers and natural numbers (excluding 1), and the implementation of bag.to.int and int.to.bag operators, which convert bags to integers based on prime factorization and vice versa.
4. Other Files: Minor changes were made to various files to add new operator kinds and integrate them into the existing framework.
   

Authors
-------------------------------------------------------------------------------

All changes in this fork were made by Yehonatan Calinsky and Yoni Zohar.
