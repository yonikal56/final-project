; COMMAND-LINE: --cegqi-all --nl-ext-tplanes
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(define-fun divisor ((a Int) (b Int)) Bool
    (exists ((k Int)) (= b (* a k)))
)
(define-fun is.a.gcd ((a Int) (b Int) (c Int)) Bool
    (and
        (divisor a b)
        (and
            (divisor a c)
            (forall ((x Int))
                (=>
                    (and (divisor x b) (divisor x c))
                    (<= x a)
                )
            )
        )
    )
)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (= (* x0 x1) 16))
;(assert (= (gcd 8 12) x0))
(declare-fun xgcd1 () Int)
(assert (= xgcd1 x0))
(assert (is.a.gcd xgcd1 8 12))
(check-sat)
