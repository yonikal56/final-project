; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
; DISABLE-TESTER: model
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
(declare-fun x12 () Int)
(declare-fun x13 () Int)
(declare-fun x14 () Int)
(declare-fun x15 () Int)
(assert (>= x0 0))
(assert (>= x1 0))
(assert (>= x2 0))
(assert (>= x3 0))
(assert (>= x4 0))
(assert (>= x5 0))
(assert (>= x6 0))
(assert (>= x7 0))
(assert (>= x8 0))
(assert (>= x9 0))
(assert (>= x10 0))
(assert (>= x11 0))
(assert (>= x12 0))
(assert (>= x13 0))
(assert (>= x14 0))
(assert (>= x15 0))
(assert (= (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10) x11) x12) x13) x14) x15) 25))
(check-sat)
