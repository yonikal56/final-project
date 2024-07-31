; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (= (* x0 x1) 15))
(assert (= (num.of.factors 12) (num.of.factors x1)))
(assert (= (num.of.factors 6) (num.of.factors 15)))
(check-sat)