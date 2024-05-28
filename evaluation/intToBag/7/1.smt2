; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 0))
(assert (>= x1 0))
(assert (distinct x1 x0))
(assert (= (* x0 x1) x0))
(check-sat)
