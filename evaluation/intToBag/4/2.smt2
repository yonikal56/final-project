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
(assert (>= x0 0))
(assert (>= x1 0))
(assert (>= x2 0))
(assert (>= x3 0))
(assert (>= x4 0))
(assert (= (* (* (* (* x0 x1) x2) x3) x4) 7))
(check-sat)
