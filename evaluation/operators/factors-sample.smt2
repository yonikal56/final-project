; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(assert (= (factors 125) (factors 25)))
(assert (= (factors -16) (factors 4)))
(check-sat)
