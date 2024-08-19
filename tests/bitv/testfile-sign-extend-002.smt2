(set-logic ALL)
(declare-const x (_ BitVec 4))
(assert (distinct ((_ extract 3 2) ((_ sign_extend 4) x)) ((_ extract 3 2) x)))
(check-sat)
