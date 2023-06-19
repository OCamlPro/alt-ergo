(set-logic BV)
(declare-const h (_ BitVec 2))
(define-fun m ((x (_ BitVec 4)) (x (_ BitVec 4)) (v (_ BitVec 4))) Bool false)
(assert (distinct false (exists ((x (_ BitVec 4))) (and (m (_ bv0 4) (_ bv0 4) (_ bv0 4)) (= ((_ sign_extend 1) x) (concat (_ bv0 1) ((_ zero_extend 2) h)))))))
(check-sat)
