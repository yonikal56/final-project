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
(declare-fun x11 () Int)
(declare-fun x12 () Int)
(declare-fun x13 () Int)
(declare-fun x14 () Int)
(declare-fun x15 () Int)
(declare-fun x16 () Int)
(declare-fun x17 () Int)
(declare-fun x18 () Int)
(declare-fun x19 () Int)
(declare-fun x20 () Int)
(declare-fun x21 () Int)
(declare-fun x22 () Int)
(declare-fun x23 () Int)
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
(assert (>= x12 1))
(assert (>= x13 1))
(assert (>= x14 1))
(assert (>= x15 1))
(assert (>= x16 1))
(assert (>= x17 1))
(assert (>= x18 1))
(assert (>= x19 1))
(assert (>= x20 1))
(assert (>= x21 1))
(assert (>= x22 1))
(assert (>= x23 1))
(assert (distinct x0 25))
(assert (distinct x0 1))
(assert (distinct x1 25))
(assert (distinct x1 1))
(assert (distinct x2 25))
(assert (distinct x2 1))
(assert (distinct x3 25))
(assert (distinct x3 1))
(assert (distinct x4 25))
(assert (distinct x4 1))
(assert (distinct x5 25))
(assert (distinct x5 1))
(assert (distinct x6 25))
(assert (distinct x6 1))
(assert (distinct x7 25))
(assert (distinct x7 1))
(assert (distinct x8 25))
(assert (distinct x8 1))
(assert (distinct x9 25))
(assert (distinct x9 1))
(assert (distinct x10 25))
(assert (distinct x10 1))
(assert (distinct x11 25))
(assert (distinct x11 1))
(assert (distinct x12 25))
(assert (distinct x12 1))
(assert (distinct x13 25))
(assert (distinct x13 1))
(assert (distinct x14 25))
(assert (distinct x14 1))
(assert (distinct x15 25))
(assert (distinct x15 1))
(assert (distinct x16 25))
(assert (distinct x16 1))
(assert (distinct x17 25))
(assert (distinct x17 1))
(assert (distinct x18 25))
(assert (distinct x18 1))
(assert (distinct x19 25))
(assert (distinct x19 1))
(assert (distinct x20 25))
(assert (distinct x20 1))
(assert (distinct x21 25))
(assert (distinct x21 1))
(assert (distinct x22 25))
(assert (distinct x22 1))
(assert (distinct x23 25))
(assert (distinct x23 1))
(assert (= (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10) x11) x12) x13) x14) x15) x16) x17) x18) x19) x20) x21) x22) x23) 25))
(assert (distinct x0 25))
(assert (distinct x0 1))
(assert (distinct x1 25))
(assert (distinct x1 1))
(assert (distinct x2 25))
(assert (distinct x2 1))
(assert (distinct x3 25))
(assert (distinct x3 1))
(assert (distinct x4 25))
(assert (distinct x4 1))
(assert (distinct x5 25))
(assert (distinct x5 1))
(assert (distinct x6 25))
(assert (distinct x6 1))
(assert (distinct x7 25))
(assert (distinct x7 1))
(assert (distinct x8 25))
(assert (distinct x8 1))
(assert (distinct x9 25))
(assert (distinct x9 1))
(assert (distinct x10 25))
(assert (distinct x10 1))
(assert (distinct x11 25))
(assert (distinct x11 1))
(assert (distinct x12 25))
(assert (distinct x12 1))
(assert (distinct x13 25))
(assert (distinct x13 1))
(assert (distinct x14 25))
(assert (distinct x14 1))
(assert (distinct x15 25))
(assert (distinct x15 1))
(assert (distinct x16 25))
(assert (distinct x16 1))
(assert (distinct x17 25))
(assert (distinct x17 1))
(assert (distinct x18 25))
(assert (distinct x18 1))
(assert (distinct x19 25))
(assert (distinct x19 1))
(assert (distinct x20 25))
(assert (distinct x20 1))
(assert (distinct x21 25))
(assert (distinct x21 1))
(assert (distinct x22 25))
(assert (distinct x22 1))
(assert (distinct x23 25))
(assert (distinct x23 1))
(check-sat)