(set-option :produce-models true)
(set-logic ALL)

(declare-const a Int)
(declare-const b Real)

(check-sat)

(get-model)
