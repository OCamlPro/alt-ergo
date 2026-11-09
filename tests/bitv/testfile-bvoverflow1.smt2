(set-logic ALL)
(declare-const x (_ BitVec 1))
(assert (bvsaddo x x))
(check-sat)
