(set-logic QF_BV)
(declare-const __ (_ BitVec 3))
(assert (and (= (_ bv0 1) ((_ extract 0 0) __)) (= (_ bv0 1) ((_ extract 2 2) __))))
(check-sat)
