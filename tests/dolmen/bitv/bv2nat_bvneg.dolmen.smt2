(set-logic ALL)

; This is true, but we are not able to prove it for now due to lack of
; algebraic reasoning on bit-vectors
(declare-const x (_ BitVec 64))
(assert (distinct (bv2nat (bvneg x)) (mod (+ (bv2nat (bvnot x)) 1) 18446744073709551616)))
(check-sat)
