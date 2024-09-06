n = list(range(2, int(input("max number of vars: "))))
result = "x0"

for i in n:
    file_name = f'test-result{result}-{i-1}.smt2'
    with open(file_name, 'w') as file:
        file.write('; COMMAND-LINE: --solve-int-as-bag\n; EXPECT: sat\n(set-logic ALL)\n(set-info :status sat)\n(set-option :incremental false)\n')
        for k in range(i):
            file.write(f'(declare-fun x{k} () Int)\n')
        for k in range(i):
            file.write(f'(assert (>= x{k} 1))\n')
        str = "(* x0 x1)"
        for k in range(2,i):
            str = f'(* {str} x{k})'
        str = f'(assert (= {str} {result}))\n'
        file.write(str)
        file.write('(check-sat)\n')