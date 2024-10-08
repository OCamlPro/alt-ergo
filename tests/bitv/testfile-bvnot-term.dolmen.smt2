(set-logic BV)

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (= x (bvnot y)))
(assert (distinct y x))
(check-sat)
