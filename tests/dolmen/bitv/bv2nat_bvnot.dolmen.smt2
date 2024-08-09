(set-logic ALL)

(declare-const x (_ BitVec 64))
(assert (distinct (bv2nat (bvnot x)) (- 18446744073709551615 (bv2nat x))))
(check-sat)
