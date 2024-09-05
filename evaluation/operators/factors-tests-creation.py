from random import randint
import numpy as np

n = list(range(2, int(input("number of tests: "))))

def create_mult(all_vars):
    return f'(* {" ".join(all_vars)})'

def originalTestsAssertion(vars):
    factor_strings = [f'(factors {var})' for var in vars]
    return f'(assert (= {" ".joib(factor_strings)}))'

def primitiveTestsAssertion(vars):
    str = '(define-fun is.prime2 ((x Int)) Bool\n(forall ((i Int))\n(=>\n(and (> i 0) (exists ((j Int)) (and (> j 0) (= x (* i j)))))\n'
    str += '(or (= x i) (= i 1))))\n)\n(define-fun divisor ((a Int) (b Int)) Bool\n(exists ((k Int)) (= b (* a k)))\n)'
    str += f'(declare-fun numfactors () Int)\n'

    for var in vars:
        str += f'(declare-fun ffactors{var} (Int) Int)\n'

    for var in vars:
        str += f'(assert (= 0 (ffactors{var} numfactors)))\n'

    return str
'''

(assert (forall ((i Int))
    (=> (and (<= 0 i) (< i numfactors12))
    (and (is.prime2 (ffactors1 i)) (is.prime2 (ffactors2 i))))
))
(assert (forall ((i Int) (j Int))
    (=> (and (<= 0 i) (< i numfactors12) (<= 0 j) (< j numfactors12)
    (distinct i j)) (distinct (ffactors1 i) (ffactors1 j)))
))
(assert (forall ((i Int) (j Int))
    (=> (and (<= 0 i) (< i numfactors12) (<= 0 j) (< j numfactors12)
    (distinct i j)) (distinct (ffactors2 i) (ffactors2 j)))
))
(assert (forall ((i Int))
    (=> (and (<= 0 i) (< i numfactors12))
    (= (ffactors1 i) (ffactors2 i)))
))
(assert (forall ((y Int))
    (=>
        (and (> y 1) (<= y 3) (is.prime2 y) (divisor y 3))
        (exists ((i Int)) (and (<= 0 i) (< i numfactors12) (= y (ffactors1 i))))
    )
))
(assert (forall ((y Int))
    (=>
        (and (> y 1) (<= y 9) (is.prime2 y) (divisor y 9))
        (exists ((i Int)) (and (<= 0 i) (< i numfactors12) (= y (ffactors2 i))))
    )
))'''


folders = ['originalTests/', 'primitiveTests/']
command_lines = ['; COMMAND-LINE: --solve-int-as-bag\n; EXPECT: sat\n(set-logic ALL)\n(set-info :status sat)\n(set-option :incremental false)\n',
                 '; COMMAND-LINE: --cegqi-all --nl-ext-tplanes\n; EXPECT: sat\n(set-logic ALL)\n(set-info :status sat)\n(set-option :incremental false)\n']
assertions = [originalTestsAssertion, primitiveTestsAssertion]
for i in n:
    for j in range(len(folders)):
        file_name = f'{folders[j]}random_test_{i}.smt2'
        with open(file_name, 'w') as file:
            file.write(command_lines[j])

            vars = [f'x{k}' for k in range(n)]

            for k in range(n):
                file.write(f'(declare-fun x{k} () Int)\n')
            for k in range(n):
                file.write(f'(assert (>= x{k} 1))\n')

            file.write(f'(assert (distinct {" ".join(vars)}))')

            file.write(assertions[j](vars))

            file.write('(check-sat)\n')