; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)
(declare-fun x9 () Int)
(declare-fun x10 () Int)
(declare-fun x11 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (>= x2 1))
(assert (>= x3 1))
(assert (>= x4 1))
(assert (>= x5 1))
(assert (>= x6 1))
(assert (>= x7 1))
(assert (>= x8 1))
(assert (>= x9 1))
(assert (>= x10 1))
(assert (>= x11 1))
(assert (distinct x1 x0))
(assert (distinct x2 x0))
(assert (distinct x3 x0))
(assert (distinct x4 x0))
(assert (distinct x5 x0))
(assert (distinct x6 x0))
(assert (distinct x7 x0))
(assert (distinct x8 x0))
(assert (distinct x9 x0))
(assert (distinct x10 x0))
(assert (distinct x11 x0))
(assert (= (* (* (* (* (* (* (* (* (* (* (* x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10) x11) x0))
(check-sat)
