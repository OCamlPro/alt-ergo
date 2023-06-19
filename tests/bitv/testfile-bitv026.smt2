(set-logic QF_BV)
(assert (= (_ bv0 1) (bvudiv (_ bv1 1) (_ bv1 1))))
(check-sat)
