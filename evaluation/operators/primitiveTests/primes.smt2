; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(define-fun is.prime2 ((x Int)) Bool
(forall ((i Int))
(=>
(and (> i 0) (exists ((j Int)) (and (> j 0) (= x (* i j)))))
(or (= x i) (= i 1))))
)
(assert (not (is.prime2 x0)))
(assert (not (is.prime2 x1)))
(assert (is.prime2 (* x0 x1)))
(check-sat)