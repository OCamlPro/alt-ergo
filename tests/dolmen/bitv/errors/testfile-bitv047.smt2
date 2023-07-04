(set-logic BV)
(assert
  (exists ((x (_ BitVec 2)))
    (and
      (bvslt x (_ bv1 2))
      (forall ((y (_ BitVec 2))) (= y (_ bv1 2))))))
(check-sat)
