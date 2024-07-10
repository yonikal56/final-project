import sympy
import math
n = list(range(2, int(input("max number to check: "))))

for i in n:
    file_name = f'test-result{i}.smt2'
    with open(file_name, 'w') as file:
        ss = 'un' if (sympy.isprime(i) or sympy.isprime(int(math.sqrt(i)) if math.sqrt(i).is_integer() else math.sqrt(i))) else ''
        file.write(f'; COMMAND-LINE: --solve-int-as-bag\n; EXPECT: {ss}sat\n(set-logic ALL)\n(set-info :status {ss}sat)\n(set-option :incremental false)\n')
        for k in range(2):
            file.write(f'(declare-fun x{k} () Int)\n')
        for k in range(2):
            file.write(f'(assert (>= x{k} 1))\n')
        for k in range(2):
            file.write(f'(assert (distinct x{k} {i}))\n')
            file.write(f'(assert (distinct x{k} 1))\n')

        file.write(f'(assert (= (* x0 x1) {i}))\n')
        for k in range(2):
            file.write(f'(assert (distinct x{k} {i}))\n')
            file.write(f'(assert (distinct x{k} 1))\n')
        file.write('(assert (distinct x0 x1))\n')
        file.write('(check-sat)\n')