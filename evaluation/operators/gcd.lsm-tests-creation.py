from random import randint
import numpy as np

n = list(range(2, int(input("max number of vars: "))+1, 2))

def create_mult(all_vars):
    return f'(* {" ".join(all_vars)})'

def split_into_pairs(lst):
    return [lst[i:i+2] for i in range(0, len(lst), 2)]

def originalTestsAssertion(pairs):
    str = ''
    for pair in pairs:
        str += f'(assert (distinct (gcd {pair[0]} {pair[1]}) (lcm {pair[0]} {pair[1]})))\n'
    return str

def primitiveTestsAssertion(pairs):
    str = '(define-fun divisor ((a Int) (b Int)) Bool\n(exists ((k Int)) (= b (* a k))))\n'
    str += '(define-fun is.a.gcd ((a Int) (b Int) (c Int)) Bool\n(and (divisor a b) (and (divisor a c) \n(forall ((x Int)) (=> (and (divisor x b) (divisor x c)) (<= x a))))))\n'
    str += '(define-fun is.a.lcm ((a Int) (b Int) (c Int)) Bool\n(exists ((k Int)) (and (is.a.gcd k b c) (= a (/ (* b c) k)))))\n'

    for pair in pairs:
        str += f'(declare-fun xgcd_{"_".join(pair)} () Int)\n'
        str += f'(declare-fun xlcm_{"_".join(pair)} () Int)\n'
        str += f'(assert (is.a.gcd xgcd_{"_".join(pair)} {pair[0]} {pair[1]}))\n'
        str += f'(assert (is.a.lcm xgcd_{"_".join(pair)} {pair[0]} {pair[1]}))\n'

    return str


folders = ['originalTests/gcd.lsm/', 'primitiveTests/gcd.lsm/']
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

            file.write(f'(assert (distinct {" ".join(vars)}))\n')

            pairs = split_into_pairs(vars)

            file.write(assertions[j](pairs))

            file.write('(check-sat)\n')