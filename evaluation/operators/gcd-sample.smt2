; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x1 () Int)
(assert (= (gcd -12 18) x1))
(assert (= x1 6))
(assert (= (gcd 30 15) 15))
(assert (= (gcd 4 9) 1))
(assert (= (gcd 0 0) 0))
(check-sat)
