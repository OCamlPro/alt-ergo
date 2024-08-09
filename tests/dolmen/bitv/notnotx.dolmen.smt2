(set-logic QF_BV)

(declare-const x (_ BitVec 64))
(assert (distinct (bvnot (bvnot x)) x))
(check-sat)
