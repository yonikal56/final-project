; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (>= x2 1))
(assert (= (* (* x0 x1) x2) 7))
(check-sat)
