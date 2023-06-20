(set-logic QF_BV)
(define-fun u () (_ BitVec 2) (_ bv1 2))
(assert (not (bvsle ((_ sign_extend 2) u) (_ bv0 4))))
(check-sat)
