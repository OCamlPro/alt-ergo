(set-logic BV)
(assert (and (exists ((U (_ BitVec 32))) true) (exists ((c (_ BitVec 32))) (= (_ bv0 32) (bvand c (_ bv1 32))))))
(check-sat)
