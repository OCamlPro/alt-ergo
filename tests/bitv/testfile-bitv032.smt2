(set-logic QF_BV)
(declare-fun b () (_ BitVec 8))
(assert (= (_ bv0 32) ((_ sign_extend 24) b)))
(check-sat)
