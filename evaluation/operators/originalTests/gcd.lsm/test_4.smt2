; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (>= x2 1))
(assert (>= x3 1))
(assert (distinct x0 x1 x2 x3))
(assert (distinct (gcd x0 x1) (lcm x0 x1)))
(assert (distinct (gcd x2 x3) (lcm x2 x3)))
(check-sat)
