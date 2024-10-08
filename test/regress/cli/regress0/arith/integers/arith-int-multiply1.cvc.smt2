; COMMAND-LINE: --solve-int-as-bag
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (= (* x0 x1) 25))
(assert (= (* x0 5) 25))
(assert (distinct x0 25))
(assert (distinct x1 25))
(assert (distinct x0 x1))
(check-sat)
