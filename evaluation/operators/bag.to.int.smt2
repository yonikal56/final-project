(set-logic ALL)
(declare-fun __intToBag_var_2 () (Bag Int))
(declare-fun __intToBag_var_3 () (Bag Int))
(assert (distinct 1 (bag.to.int (as bag.empty (Bag Int)))))
(check-sat)