; COMMAND-LINE: --cegqi-all --nl-ext-tplanes
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (distinct x0 x1 1))
(define-fun is.prime2 ((x Int)) Bool
(forall ((i Int))
(=>
(and (> i 0) (exists ((j Int)) (and (> j 0) (= x (* i j)))))
(or (= x i) (= i 1))))
)
(define-fun divisor ((a Int) (b Int)) Bool
(exists ((k Int)) (= b (* a k))))
(declare-fun numfactors () Int)
(declare-fun ffactorsx0 (Int) Int)
(declare-fun ffactorsx1 (Int) Int)
(assert (= 0 (ffactorsx0 numfactors)))
(assert (= 0 (ffactorsx1 numfactors)))
(assert (forall ((i Int))
(=> (and (<= 0 i) (< i numfactors))
(and (is.prime2 (ffactorsx0 i)) (is.prime2 (ffactorsx1 i))))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx0 i) (ffactorsx0 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx1 i) (ffactorsx1 j)))
))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x0) (is.prime2 y) (divisor y x0))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx0 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x1) (is.prime2 y) (divisor y x1))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx1 i)))))))
(check-sat)