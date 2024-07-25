; COMMAND-LINE: --solve-int-as-bag
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
(define-fun is.a.lcm ((a Int) (b Int) (c Int)) Bool
    (exists ((k Int))
        (and (is.a.gcd k b c)
        (= a (/ (* b c) k))
        )
    )
)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (= (* x0 x1) 24))
;(assert (distinct x1 4))
(assert (distinct x1 1))
(assert (distinct x1 24))
;(assert (= (lcm x0 7) 42))
(declare-fun xlcm1 () Int)
(assert (= xlcm1 42))
(assert (is.a.lcm xlcm1 x0 7))
(check-sat)
