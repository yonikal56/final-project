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
(assert (= (* (* (* (* (* (* (* x0 x1) x2) x3) x4) x5) x6) x7) 25))
(assert (= (* x0 5) 25))
(check-sat)
