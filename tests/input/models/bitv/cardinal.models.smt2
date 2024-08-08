(set-logic BV)
(set-option :produce-models true)

; We used to be able to reply 'unsat' here, but using unsound reasoning.
; We should be able to reply 'unsat' again when we start propagating [distinct]
; constraints in the bit-vector domain
(declare-const a (_ BitVec 1))
(declare-const b (_ BitVec 1))
(declare-const c (_ BitVec 1))
(assert (distinct a b c))
(check-sat)
