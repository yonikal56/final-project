; COMMAND-LINE: --solve-int-as-bag
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (>= x2 1))
(assert (>= x3 1))
(assert (>= x4 1))
(assert (>= x5 1))
(assert (>= x6 1))
(assert (distinct x0 5))
(assert (distinct x0 1))
(assert (distinct x1 5))
(assert (distinct x1 1))
(assert (distinct x2 5))
(assert (distinct x2 1))
(assert (distinct x3 5))
(assert (distinct x3 1))
(assert (distinct x4 5))
(assert (distinct x4 1))
(assert (distinct x5 5))
(assert (distinct x5 1))
(assert (distinct x6 5))
(assert (distinct x6 1))
(assert (= (* (* (* (* (* (* x0 x1) x2) x3) x4) x5) x6) 5))
(assert (distinct x0 5))
(assert (distinct x0 1))
(assert (distinct x1 5))
(assert (distinct x1 1))
(assert (distinct x2 5))
(assert (distinct x2 1))
(assert (distinct x3 5))
(assert (distinct x3 1))
(assert (distinct x4 5))
(assert (distinct x4 1))
(assert (distinct x5 5))
(assert (distinct x5 1))
(assert (distinct x6 5))
(assert (distinct x6 1))
(check-sat)
