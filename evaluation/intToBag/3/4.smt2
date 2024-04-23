; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (= (* x0 x1) 27))
(assert (distinct x0 27))
(assert (distinct x0 9))
(assert (distinct x1 27))
(assert (distinct x1 3))
(assert (distinct x0 1))
(assert (distinct x1 1))
(assert (distinct x0 x1))
(check-sat)
