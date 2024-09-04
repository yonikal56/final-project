; COMMAND-LINE: --solve-int-as-bag
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :incremental false)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (>= x 1))
(assert (>= y 1))
(assert (>= z 1))
(assert (=>
(and (exists ((k Int)) (and (>= k 1) (= y (* x k)))) (exists ((j Int)) (and (>= j 1) (= z (* y j)))))
(exists ((m Int)) (and (>= m 1) (= z (* x m))))
))
(check-sat)
