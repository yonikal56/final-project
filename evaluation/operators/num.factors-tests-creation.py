from random import randint
import numpy as np

n = list(range(2, int(input("max number of vars: "))))

def create_mult(all_vars):
    return f'(* {" ".join(all_vars)})'

def originalTestsAssertion(vars):
    factor_strings = [f'(num.of.factors {var})' for var in vars]
    return f'(assert (= {" ".join(factor_strings)}))\n'

def primitiveTestsAssertion(vars):
    str = '(define-fun is.prime2 ((x Int)) Bool\n(forall ((i Int))\n(=>\n(and (> i 0) (exists ((j Int)) (and (> j 0) (= x (* i j)))))\n'
    str += '(or (= x i) (= i 1))))\n)\n(define-fun divisor ((a Int) (b Int)) Bool\n(exists ((k Int)) (= b (* a k))))\n'
    str += f'(declare-fun numfactors () Int)\n'

    for var in vars:
        str += f'(declare-fun ffactors{var} (Int) Int)\n'

    for var in vars:
        str += f'(assert (= 0 (ffactors{var} numfactors)))\n'

    prime_strs = [f'(is.prime2 (ffactors{var} i))' for var in vars]

    str += f'(assert (forall ((i Int))\n(=> (and (<= 0 i) (< i numfactors))\n(and {" ".join(prime_strs)}))\n))\n'

    for var in vars:
        str += f'(assert (forall ((i Int) (j Int))\n(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)\n(distinct i j)) (distinct (ffactors{var} i) (ffactors{var} j)))\n))\n'

    for var in vars:
        str += f'(assert (forall ((y Int))\n(=> (and (> y 1) (<= y {var}) (is.prime2 y) (divisor y {var}))\n(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactors{var} i)))))))\n'

    return str


folders = ['originalTests/num.factors/', 'primitiveTests/num.factors/']
command_lines = ['; COMMAND-LINE: --solve-int-as-bag\n; EXPECT: sat\n(set-logic ALL)\n(set-info :status sat)\n(set-option :incremental false)\n',
                 '; COMMAND-LINE: --cegqi-all --nl-ext-tplanes\n; EXPECT: sat\n(set-logic ALL)\n(set-info :status sat)\n(set-option :incremental false)\n']
assertions = [originalTestsAssertion, primitiveTestsAssertion]
for i in n:
    for j in range(len(folders)):
        file_name = f'{folders[j]}test_{i}.smt2'
        with open(file_name, 'w') as file:
            file.write(command_lines[j])

            vars = [f'x{str(k)}' for k in range(i)]

            for k in range(i):
                file.write(f'(declare-fun x{k} () Int)\n')
            for k in range(i):
                file.write(f'(assert (>= x{k} 1))\n')

            file.write(f'(assert (distinct {" ".join(vars)} 1))\n')

            file.write(assertions[j](vars))

            file.write('(check-sat)\n')