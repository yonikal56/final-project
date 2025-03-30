; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (not (is.prime x0)))
(assert (not (is.prime x1)))
(assert (is.prime (* x0 x1)))
(check-sat)