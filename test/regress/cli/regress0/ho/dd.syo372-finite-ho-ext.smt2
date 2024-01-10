(set-logic HO_ALL)
(set-info :status sat)
(declare-sort U 0)
(declare-sort V 0)
(declare-fun t (U) Bool)
(declare-fun p ((-> U Bool)) V)
(declare-fun tp (U) Bool)
(assert (not (= (p tp) (p t))))
(check-sat)
