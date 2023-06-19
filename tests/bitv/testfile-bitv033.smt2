(set-logic QF_BV)
(define-fun t () (_ BitVec 2) (_ bv0 2))
(assert (not (= (_ bv0 2) (bvand t (bvand t (_ bv0 2))))))
(check-sat)
