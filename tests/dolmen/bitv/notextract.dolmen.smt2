(set-logic QF_BV)

(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))

(assert (= ((_ extract 32 16) x) (bvnot ((_ extract 32 16) y))))
(assert (= ((_ extract 32 0) x) ((_ extract 32 0) y)))
(check-sat)
