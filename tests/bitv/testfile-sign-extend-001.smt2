(set-logic ALL)
(declare-const x (_ BitVec 4))
(assert (distinct ((_ extract 5 2) ((_ sign_extend 4) x)) (concat ((_ extract 3 3) x) (concat ((_ extract 3 3) x) ((_ extract 3 2) x)))))
(check-sat)
