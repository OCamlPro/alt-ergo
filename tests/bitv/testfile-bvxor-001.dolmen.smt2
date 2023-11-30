(set-logic ALL)
(declare-const x (_ BitVec 8))
(assert (= x (bvxor #b10100101 x)))
(check-sat)
