(set-logic QF_ALL)
(declare-fun bv_set () (Set (_ BitVec 4)))
(assert (= (card bv_set) 5))
(check-sat)
