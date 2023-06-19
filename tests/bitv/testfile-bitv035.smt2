(set-logic QF_BV)

(declare-fun T () (_ BitVec 4))

(assert (=
  (_ bv0 4)
  (bvand
    (_ bv1 4)
    ((_ extract 3 0)
      (bvand ((_ zero_extend 12) T) (_ bv3 16))
    )
  )
))

(check-sat)
