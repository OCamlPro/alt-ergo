(set-logic QF_BV)

(declare-const x (_ BitVec 3))
(assert (= ((_ extract 1 0) x) (bvnot ((_ extract 2 1) x))))
(assert (= ((_ extract 0 0) x) #b0))
(assert (distinct x #b010))
(check-sat)
