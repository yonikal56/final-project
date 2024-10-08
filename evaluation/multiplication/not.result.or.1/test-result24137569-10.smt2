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
(declare-fun x7 () Int)
(declare-fun x8 () Int)
(declare-fun x9 () Int)
(declare-fun x10 () Int)
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
(assert (distinct x0 24137569))
(assert (distinct x0 1))
(assert (distinct x1 24137569))
(assert (distinct x1 1))
(assert (distinct x2 24137569))
(assert (distinct x2 1))
(assert (distinct x3 24137569))
(assert (distinct x3 1))
(assert (distinct x4 24137569))
(assert (distinct x4 1))
(assert (distinct x5 24137569))
(assert (distinct x5 1))
(assert (distinct x6 24137569))
(assert (distinct x6 1))
(assert (distinct x7 24137569))
(assert (distinct x7 1))
(assert (distinct x8 24137569))
(assert (distinct x8 1))
(assert (distinct x9 24137569))
(assert (distinct x9 1))
(assert (distinct x10 24137569))
(assert (distinct x10 1))
(assert (= (* (* (* (* (* (* (* (* (* (* x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10) 24137569))
(assert (distinct x0 24137569))
(assert (distinct x0 1))
(assert (distinct x1 24137569))
(assert (distinct x1 1))
(assert (distinct x2 24137569))
(assert (distinct x2 1))
(assert (distinct x3 24137569))
(assert (distinct x3 1))
(assert (distinct x4 24137569))
(assert (distinct x4 1))
(assert (distinct x5 24137569))
(assert (distinct x5 1))
(assert (distinct x6 24137569))
(assert (distinct x6 1))
(assert (distinct x7 24137569))
(assert (distinct x7 1))
(assert (distinct x8 24137569))
(assert (distinct x8 1))
(assert (distinct x9 24137569))
(assert (distinct x9 1))
(assert (distinct x10 24137569))
(assert (distinct x10 1))
(check-sat)
