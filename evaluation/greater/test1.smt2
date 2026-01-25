; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (= (* x0 x1) 7))
(assert (distinct x1 -1))
(assert (distinct x1 -7))
(assert (>= x1 2))
(check-sat)









;(assert (= (* x0 x1) 12))
;(assert (distinct x0 12))
;(assert (distinct x0 1))
;(assert (distinct x1 12))
;(assert (distinct x1 1))
;(assert (distinct x0 x1))