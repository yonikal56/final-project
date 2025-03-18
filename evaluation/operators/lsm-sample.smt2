; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x1 () Int)
(assert (= (lcm -4 6) x1))
(assert (= x1 12))
(assert (= (lcm 4 -5) 20))
(assert (= (lcm 0 1) 0))
(assert (= (lcm 1 0) 0))
(assert (= (lcm 0 0) 0))
(check-sat)
