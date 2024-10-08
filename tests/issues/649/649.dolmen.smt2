(set-logic BV)
(declare-const x (_ BitVec 2))
(assert (
    exists
      ((y (_ BitVec 4)))
      (distinct
        (concat (concat ((_ extract 3 3) y) ((_ extract 3 3) y)) y)
        (concat (concat (_ bv0 2) x) (_ bv0 2))
)))
(check-sat)
