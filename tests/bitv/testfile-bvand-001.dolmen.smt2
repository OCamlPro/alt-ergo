(set-logic ALL)
(declare-const x (_ BitVec 8))
(assert (distinct #b00000000 (bvand x (bvnot x))))
(check-sat)
