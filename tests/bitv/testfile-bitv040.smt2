(set-logic QF_BV)
(assert (= (_ bv0 1) (bvcomp (_ bv0 1) (_ bv0 1))))
(check-sat)
