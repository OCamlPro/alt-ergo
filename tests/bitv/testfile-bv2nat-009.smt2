(set-logic ALL)
(declare-const x (_ BitVec 32))
(assert (distinct (bv2nat (concat #x00000000 x)) (bv2nat x)))
(check-sat)
