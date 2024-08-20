; COMMAND-LINE: --solve-int-as-bag
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
(define-fun divisor ((a Int) (b Int)) Bool
    (exists ((k Int)) (= b (* a k)))
)
;factors of 3 = factors of 9 (numoffactors = 1)
(declare-fun ffactors1 (Int) Int)
(declare-fun ffactors2 (Int) Int)
(declare-fun numfactors12 () Int)
(assert (= numfactors12 1))
(assert (= 0 (ffactors1 numfactors12)))
(assert (= 0 (ffactors2 numfactors12)))
(assert (forall ((i Int))
    (=> (and (<= 0 i) (< i numfactors12))
    (and (is.prime2 (ffactors1 i)) (is.prime2 (ffactors2 i))))
))
(assert (forall ((i Int) (j Int))
    (=> (and (<= 0 i) (< i numfactors12) (<= 0 j) (< j numfactors12)
    (distinct i j)) (distinct (ffactors1 i) (ffactors1 j)))
))
(assert (forall ((i Int) (j Int))
    (=> (and (<= 0 i) (< i numfactors12) (<= 0 j) (< j numfactors12)
    (distinct i j)) (distinct (ffactors2 i) (ffactors2 j)))
))
(assert (forall ((i Int))
    (=> (and (<= 0 i) (< i numfactors12))
    (= (ffactors1 i) (ffactors2 i)))
))
(assert (forall ((y Int))
    (=>
        (and (> y 1) (<= y 3) (is.prime2 y) (divisor y 3))
        (exists ((i Int)) (and (<= 0 i) (< i numfactors12) (= y (ffactors1 i))))
    )
))
(assert (forall ((y Int))
    (=>
        (and (> y 1) (<= y 9) (is.prime2 y) (divisor y 9))
        (exists ((i Int)) (and (<= 0 i) (< i numfactors12) (= y (ffactors2 i))))
    )
))
(check-sat)