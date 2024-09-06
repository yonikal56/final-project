; COMMAND-LINE: --cegqi-all --nl-ext-tplanes
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (>= x0 1))
(assert (>= x1 1))
(assert (distinct x0 x1))
(define-fun divisor ((a Int) (b Int)) Bool
(exists ((k Int)) (= b (* a k))))
(define-fun is.a.gcd ((a Int) (b Int) (c Int)) Bool
(and (divisor a b) (and (divisor a c) 
(forall ((x Int)) (=> (and (divisor x b) (divisor x c)) (<= x a))))))
(define-fun is.a.lcm ((a Int) (b Int) (c Int)) Bool
(exists ((k Int)) (and (is.a.gcd k b c) (= a (/ (* b c) k)))))
(declare-fun xgcd_x0_x1 () Int)
(declare-fun xlcm_x0_x1 () Int)
(assert (is.a.gcd xgcd_x0_x1 x0 x1))
(assert (is.a.lcm xgcd_x0_x1 x0 x1))
(check-sat)
