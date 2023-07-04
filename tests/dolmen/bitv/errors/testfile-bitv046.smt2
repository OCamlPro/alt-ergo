(set-logic BV)
(assert
  (distinct
    (exists
      ((x (_ BitVec 2)))
      (= (_ bv0 2) (bvashr x (_ bv0 2))))
    (exists
      ((y (_ BitVec 2)))
      (= (_ bv0 2) (bvand y (_ bv0 2))))))
(check-sat)
