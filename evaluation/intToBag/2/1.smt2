; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (= (* x0 x1) 25))
(assert (distinct x0 25))
(assert (distinct x1 25))
(assert (distinct x0 1))
(assert (distinct x1 1))
(check-sat)
