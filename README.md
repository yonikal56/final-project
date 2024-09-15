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

### Mapping from $\(\mathbb{Z} \to \mathbb{N} \setminus \\{0, 1\\}\)$:

Define the function $\( g: \mathbb{Z} \to \mathbb{N} \setminus \\{0, 1\\} \)$ as follows:

```math
g(z) = 
\begin{cases}
2z + 2 & \text{if } z \geq 0, \\
-2z + 1 & \text{if } z < 0.
\end{cases}
```
This mapping ensures that all results are within the set $\(\{2, 3, 4, \ldots\}\)$.

### Inverse Mapping from $\(\mathbb{N} \setminus \\{0, 1\\} \to \mathbb{Z}\)$:

Define the inverse function $\( g^{-1}: \mathbb{N} \setminus \\{0, 1\\} \to \mathbb{Z} \)$ as follows:

```math
g^{-1}(n) = 
\begin{cases}
\frac{n}{2} - 1 & \text{if } n \text{ is even}, \\
-\frac{n - 1}{2} & \text{if } n \text{ is odd}.
\end{cases}
```

### Example:

- For $z = 3$: $g(3) = 2 \times 3 + 2 = \textbf{8}$}
- For $z = -3$: $g(-3) = -2 \times (-3) + 1 = \textbf{7}$
- For $n = 8$: $g^{-1}(8) = \frac{8}{2} - 1 = \textbf{3}$
- For $n = 7$: $g^{-1}(7) = -\frac{7 - 1}{2} = \textbf{-3}$

### New operators

In addition to this transformation, new operators have been implemented based on this idea:
1. **gcd** (greatest common divisor)
2. **lcm** (least common multiple)
3. **is_prime** (checks if a number is prime)
4. **factors** (lists the prime factors of a number)
5. **num_of_factors** (counts the number of different prime factors of a number)

### Translation of Integer Operators to Bag Operators

The supported integer operators are translated to equivalent bag operators, with each integer first converted to its bag representation as described:

1. **integer multiplication** – translated to the union of disjoint bags.
2. **gcd** – represented as the intersection of bags, where the multiplicity of each element is the minimum of its multiplicities in the two bags.
3. **lcm** – represented as the union of bags, where the multiplicity of each element is the maximum of its multiplicities.
4. **is_prime** – the bag's cardinality equals 1 (i.e., the bag contains only one distinct element).
5. **factors** – the set of distinct bag elements.
6. **num_of_factors** – the cardinality of the set of distinct bag elements.


### How to use the feature

1. **Build CVC5**:
   Follow the standard CVC5 build instructions from [here](https://github.com/cvc5/cvc5/blob/main/INSTALL.rst).

2. **Running an Example**:
   To run CVC5 on the `evaluation/multiplication/equals/test-result1-10.smt2` file, use the command:
   ```bash
   ./build/bin/cvc5 evaluation/multiplication/equals/test-result1-10.smt2
   ```

3. **Using the New Feature**:
   To enable the new integer-to-bag transformation feature (and the other operators), add the `--solve-int-as-bag` flag:
   ```bash
   ./build/bin/cvc5 evaluation/multiplication/equals/test-result1-10.smt2 --solve-int-as-bag
   ```

4. **Dumping Models**:
   If you wish to see the models for satisfiable (SAT) tests, include the `--dump-models` flag as follows:
   ```bash
   ./build/bin/cvc5 evaluation/multiplication/equals/test-result1-10.smt2 --solve-int-as-bag --dump-models
   ```


Test Results
-------------------------------------------------------------------------------

We compared the performance of CVC5 with and without our preprocessing pass. All tests included either multiplication or the newly implemented operators. For the new operators, we created equivalent tests without using them directly, since CVC5 does not natively support these operators without our option.
We ran CVC5 three times for each test: first without any additional options, then with the --cegqi-all --nl-ext-tplanes flags (which enable more efficient arithmetic solving in CVC5), and finally with our new feature enabled.

All tests are organized into the following subfolders within the "evaluation" folder:
1. multiplication: Contains various tests involving multiplication.
2. operators: Contains tests for the new operators in two forms:
   - original: Using the new operators.
   - primitive: Using pure CVC5 logic without the new operators.
3. randomTests: Contains randomly generated tests that involve only multiplication.
Each folder includes Python scripts for generating tests and Bash scripts for comparing the results.

Tests were executed on a large cluster, and a detailed comparison of the results can be found in the "tests_results_on_cluster.txt" file.

A total review of the results is:
| Test Configuration                                 | Status | Total | Solved | SAT  | UNSAT | Best | Timeout | Error | Uniq | Time (CPU) | Memory (MB) |
|----------------------------------------------------|--------|-------|--------|------|-------|------|---------|-------|------|------------|-------------|
| No Bags (no flags)                                 | OK     | 1110  | 353    | 294  | 59    | 111  | 739     | 1     | 0    | 7970.7     | 15913.3     |
| No Bags (--cegqi-all --nl-ext-tplanes flags)       | OK     | 1110  | 354    | 294  | 60    | 227  | 755     | 1     | 0    | 8037.1     | 15285.2     |
| With Bags (new feature, --solve-int-as-bag flag)   | OK     | 1110  | 895    | 603  | 292   | 810  | 220     | 0     | 541  | 4210.9     | 22058.7     |

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
