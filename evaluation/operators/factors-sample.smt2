; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(assert (same.factors 125 25))
(assert (same.factors 4 -16))
(assert (not (same.factors 4 9)))
(check-sat)
