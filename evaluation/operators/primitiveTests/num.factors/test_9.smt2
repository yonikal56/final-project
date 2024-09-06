; COMMAND-LINE: --cegqi-all --nl-ext-tplanes
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
(assert (>= x0 1))
(assert (>= x1 1))
(assert (>= x2 1))
(assert (>= x3 1))
(assert (>= x4 1))
(assert (>= x5 1))
(assert (>= x6 1))
(assert (>= x7 1))
(assert (>= x8 1))
(assert (distinct x0 x1 x2 x3 x4 x5 x6 x7 x8 1))
(define-fun is.prime2 ((x Int)) Bool
(forall ((i Int))
(=>
(and (> i 0) (exists ((j Int)) (and (> j 0) (= x (* i j)))))
(or (= x i) (= i 1))))
)
(define-fun divisor ((a Int) (b Int)) Bool
(exists ((k Int)) (= b (* a k)))
)(declare-fun numfactors () Int)
(declare-fun ffactorsx0 (Int) Int)
(declare-fun ffactorsx1 (Int) Int)
(declare-fun ffactorsx2 (Int) Int)
(declare-fun ffactorsx3 (Int) Int)
(declare-fun ffactorsx4 (Int) Int)
(declare-fun ffactorsx5 (Int) Int)
(declare-fun ffactorsx6 (Int) Int)
(declare-fun ffactorsx7 (Int) Int)
(declare-fun ffactorsx8 (Int) Int)
(assert (= 0 (ffactorsx0 numfactors)))
(assert (= 0 (ffactorsx1 numfactors)))
(assert (= 0 (ffactorsx2 numfactors)))
(assert (= 0 (ffactorsx3 numfactors)))
(assert (= 0 (ffactorsx4 numfactors)))
(assert (= 0 (ffactorsx5 numfactors)))
(assert (= 0 (ffactorsx6 numfactors)))
(assert (= 0 (ffactorsx7 numfactors)))
(assert (= 0 (ffactorsx8 numfactors)))
(assert (forall ((i Int))
(=> (and (<= 0 i) (< i numfactors))
(and (is.prime2 (ffactorsx0 i)) (is.prime2 (ffactorsx1 i)) (is.prime2 (ffactorsx2 i)) (is.prime2 (ffactorsx3 i)) (is.prime2 (ffactorsx4 i)) (is.prime2 (ffactorsx5 i)) (is.prime2 (ffactorsx6 i)) (is.prime2 (ffactorsx7 i)) (is.prime2 (ffactorsx8 i))))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx0 i) (ffactorsx0 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx1 i) (ffactorsx1 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx2 i) (ffactorsx2 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx3 i) (ffactorsx3 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx4 i) (ffactorsx4 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx5 i) (ffactorsx5 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx6 i) (ffactorsx6 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx7 i) (ffactorsx7 j)))
))
(assert (forall ((i Int) (j Int))
(=> (and (<= 0 i) (< i numfactors) (<= 0 j) (< j numfactors)
(distinct i j)) (distinct (ffactorsx8 i) (ffactorsx8 j)))
))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x0) (is.prime2 y) (divisor y x0))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx0 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x1) (is.prime2 y) (divisor y x1))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx1 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x2) (is.prime2 y) (divisor y x2))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx2 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x3) (is.prime2 y) (divisor y x3))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx3 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x4) (is.prime2 y) (divisor y x4))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx4 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x5) (is.prime2 y) (divisor y x5))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx5 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x6) (is.prime2 y) (divisor y x6))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx6 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x7) (is.prime2 y) (divisor y x7))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx7 i)))))))
(assert (forall ((y Int))
(=> (and (> y 1) (<= y x8) (is.prime2 y) (divisor y x8))
(exists ((i Int)) (and (<= 0 i) (< i numfactors) (= y (ffactorsx8 i)))))))
(check-sat)
