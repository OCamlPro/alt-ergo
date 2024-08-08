(set-logic ALL)
(set-option :produce-models true)

(declare-const x (_ BitVec 64))
(assert (not (and (<= (bv2nat (bvnot x)) 18446744073709551615) (<= 0 (bv2nat (bvnot x))))))
(check-sat)
