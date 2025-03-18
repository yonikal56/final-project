; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x1 () Int)
(assert (is.prime 5))
(assert (is.prime 7))
(assert (not (is.prime -7)))
(assert (not (is.prime -1)))
(assert (not (is.prime 1)))
(check-sat)
