; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (= (* x0 x1) 25))
(assert (= (* x0 5) 25))
(check-sat)
