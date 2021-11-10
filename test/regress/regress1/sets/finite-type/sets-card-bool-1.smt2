(set-logic ALL)
(set-info :status unsat)
(set-option :produce-models true)
(set-option :sets-ext true)
(declare-fun A () (Set Bool))
(declare-fun B () (Set Bool))
(declare-fun universe () (Set Bool))
(assert (= (set.card A) 2))
(assert (= (set.card B) 2))
(assert (= (set.inter A B) (as set.empty (Set Bool))))
(assert (= universe (as set.universe (Set Bool))))
(check-sat)
