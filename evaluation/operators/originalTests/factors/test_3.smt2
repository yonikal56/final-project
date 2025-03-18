; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (distinct x0 x1 x2))
(assert (same.factors x0 x1))
(assert (same.factors x1 x2))
(check-sat)
