(set-logic ALL)
(declare-const x (_ BitVec 8))
(assert (distinct #b11111111 (bvor x (bvnot x))))
(check-sat)
