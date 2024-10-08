(set-logic QF_BV)
(declare-fun T () (_ BitVec 2))
(assert
  (and
    (distinct T (_ bv0 2))
    (= (_ bv0 2) (concat (_ bv0 1) ((_ extract 0 0) T)))))
(check-sat)
