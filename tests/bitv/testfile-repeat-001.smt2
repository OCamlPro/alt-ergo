(set-logic ALL)
(declare-const x (_ BitVec 4))
(assert (distinct ((_ extract 5 4) ((_ repeat 10) x)) ((_ extract 1 0) x)))
(check-sat)
