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
(declare-fun x24 () Int)
(declare-fun x25 () Int)
(declare-fun x26 () Int)
(declare-fun x27 () Int)
(declare-fun x28 () Int)
(declare-fun x29 () Int)
(declare-fun x30 () Int)
(declare-fun x31 () Int)
(declare-fun x32 () Int)
(declare-fun x33 () Int)
(declare-fun x34 () Int)
(declare-fun x35 () Int)
(declare-fun x36 () Int)
(declare-fun x37 () Int)
(declare-fun x38 () Int)
(declare-fun x39 () Int)
(declare-fun x40 () Int)
(declare-fun x41 () Int)
(declare-fun x42 () Int)
(declare-fun x43 () Int)
(declare-fun x44 () Int)
(declare-fun x45 () Int)
(declare-fun x46 () Int)
(declare-fun x47 () Int)
(declare-fun x48 () Int)
(declare-fun x49 () Int)
(declare-fun x50 () Int)
(declare-fun x51 () Int)
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
(assert (>= x24 1))
(assert (>= x25 1))
(assert (>= x26 1))
(assert (>= x27 1))
(assert (>= x28 1))
(assert (>= x29 1))
(assert (>= x30 1))
(assert (>= x31 1))
(assert (>= x32 1))
(assert (>= x33 1))
(assert (>= x34 1))
(assert (>= x35 1))
(assert (>= x36 1))
(assert (>= x37 1))
(assert (>= x38 1))
(assert (>= x39 1))
(assert (>= x40 1))
(assert (>= x41 1))
(assert (>= x42 1))
(assert (>= x43 1))
(assert (>= x44 1))
(assert (>= x45 1))
(assert (>= x46 1))
(assert (>= x47 1))
(assert (>= x48 1))
(assert (>= x49 1))
(assert (>= x50 1))
(assert (>= x51 1))
(assert (= (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* (* x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10) x11) x12) x13) x14) x15) x16) x17) x18) x19) x20) x21) x22) x23) x24) x25) x26) x27) x28) x29) x30) x31) x32) x33) x34) x35) x36) x37) x38) x39) x40) x41) x42) x43) x44) x45) x46) x47) x48) x49) x50) x51) 1))
(check-sat)