(set-logic ALL)
(set-info :status sat)
(declare-fun a () Int)
(assert (distinct 0.0 (/ a (+ 0.5 a))))
(check-sat)