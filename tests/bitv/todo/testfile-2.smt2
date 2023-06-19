(set-logic QF_BV)
(assert (= (_ bv0 1) (bvnot (ite false (_ bv1 1) (_ bv0 1)))))
(check-sat)
