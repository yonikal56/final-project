; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x1 () Int)
(assert (= (num.of.factors 125) (num.of.factors 2)))
(assert (= (num.of.factors 6) (num.of.factors -10)))
(check-sat)
