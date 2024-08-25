from random import randint
import numpy as np

n = list(range(int(input("number of tests: "))))

def create_mult(all_vars):
    return f'(* {" ".join(all_vars)})'

for i in n:
    file_name = f'random_test_{i}.smt2'
    with open(file_name, 'w') as file:
        file.write('; COMMAND-LINE: --solve-int-as-bag\n(set-logic ALL)\n(set-option :incremental false)\n')
        number_of_x = randint(5, 100)
        number_of_consts = randint(2, 5)
        consts = [randint(2, 1000) for _ in range(number_of_consts)]
        x_vars = [f'x{k}' for k in range(number_of_x)]
        all_vars = x_vars + consts
        all_number = len(all_vars)
        for k in range(number_of_x):
            file.write(f'(declare-fun x{k} () Int)\n')
        for k in range(number_of_x):
            file.write(f'(assert (>= x{k} 1))\n')

        number_of_asserts = randint(1, 10)
        operators = ['=', 'distinct']
        for _ in range(number_of_asserts):
            number_left = randint(2, all_number)
            number_right = randint(2, all_number)
            str = f'(assert ({np.random.choice(operators)} {create_mult(np.random.choice(all_vars, number_left, replace=False))} {create_mult(np.random.choice(all_vars, number_right, replace=False))}))\n'
            file.write(str)

        file.write('(check-sat)\n')