(set-logic ALL)

(declare-const x (_ BitVec 64))
(assert (distinct (bv2nat (bvneg x)) (mod (+ (bv2nat (bvnot x)) 1) 18446744073709551616)))
(check-sat)
