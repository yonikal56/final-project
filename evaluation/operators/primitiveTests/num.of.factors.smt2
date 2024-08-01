; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
;(set-info :status sat)
(set-option :incremental false)
(define-fun is.prime2 ((x Int)) Bool
    (forall ((i Int))
        (=>
            (and (> i 0) (exists ((j Int)) (and (> j 0) (= x (* i j)))))
            (or (= x i) (= i 1))))
)
(define-fun divisor ((a Int) (b Int)) Bool
    (exists ((k Int)) (= b (* a k)))
)
(declare-fun ffactors1 (Int) Int)
(declare-fun numfactors1 () Int)
(assert (= numfactors1 1))
(assert (= 0 (ffactors1 numfactors1)))
(assert (forall ((i Int))
    (=> (and (<= 0 i) (< i numfactors1)) (is.prime2 (ffactors1 i)))
))
(assert (forall ((i Int) (j Int))
    (=> (and (<= 0 i) (< i numfactors1) (<= 0 j) (< j numfactors1)
    (distinct i j)) (distinct (ffactors1 i) (ffactors1 j)))
))
(assert (forall ((y Int))
    (=>
        (and (> y 1) (<= y 3) (is.prime2 y) (divisor y 3)) (exists ((i Int)) (and (<= 0 i) (< i numfactors1) (= y (ffactors1 i))))
    )
))
(check-sat)
;(assert (= (num.of.factors 12) (num.of.factors x1)))
;(assert (= (num.of.factors 6) (num.of.factors 15)))
