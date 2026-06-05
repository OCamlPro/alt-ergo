(set-option :produce-models true)
(set-logic ALL)

(declare-const a Bool)

(assert (=> a true))

(check-sat)
(get-model)
