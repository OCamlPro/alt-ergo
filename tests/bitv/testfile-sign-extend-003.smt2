(set-logic ALL)
(declare-const x (_ BitVec 4))
(assert (distinct ((_ extract 5 4) ((_ sign_extend 4) x)) ((_ repeat 2) ((_ extract 3 3) x))))
(check-sat)
