(set-logic QF_BV)
(declare-const T (_ BitVec 1))
(assert (= (_ bv1 32) ((_ zero_extend 24) ((_ zero_extend 7) T))))
(check-sat)
