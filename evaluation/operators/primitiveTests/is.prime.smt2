; COMMAND-LINE: --cegqi-all --nl-ext-tplanes
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(define-fun is.prime2 ((x Int)) Bool
    (forall ((i Int))
        (=>
            (and (> i 0) (exists ((j Int)) (and (> j 0) (= x (* i j)))))
            (or (= x i) (= i 1))))
)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (= (* x0 x1) 6))
(assert (distinct x1 6))
(assert (distinct x1 3))
(assert (is.prime2 x0))
(check-sat)
