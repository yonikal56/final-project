; COMMAND-LINE: --solve-int-as-bag
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (>= x2 1))
(assert (distinct x0 97))
(assert (distinct x0 1))
(assert (distinct x1 97))
(assert (distinct x1 1))
(assert (distinct x2 97))
(assert (distinct x2 1))
(assert (= (* (* x0 x1) x2) 97))
(assert (distinct x0 97))
(assert (distinct x0 1))
(assert (distinct x1 97))
(assert (distinct x1 1))
(assert (distinct x2 97))
(assert (distinct x2 1))
(check-sat)
