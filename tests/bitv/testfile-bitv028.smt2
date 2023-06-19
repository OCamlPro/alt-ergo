(set-logic BV)
(assert (exists ((X (_ BitVec 4))) (= (_ bv0 4) (bvand X (_ bv1 4)))))
(check-sat)
