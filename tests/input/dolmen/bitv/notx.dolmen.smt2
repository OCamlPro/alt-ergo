(set-logic QF_BV)

(declare-const x (_ BitVec 64))
(assert (= (bvnot x) x))
(check-sat)
