; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (= (* x0 x1) 24))
;(assert (distinct x1 4))
(assert (distinct x1 1))
(assert (distinct x1 24))
(assert (= (lcm x0 7) 42))
(check-sat)