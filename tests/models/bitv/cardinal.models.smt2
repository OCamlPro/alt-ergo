(set-logic BV)
(set-option :produce-models true)

; Without :produce-models we say 'unknown', not 'unsat'
(declare-const a (_ BitVec 1))
(declare-const b (_ BitVec 1))
(declare-const c (_ BitVec 1))
(assert (distinct a b c))
(check-sat)
