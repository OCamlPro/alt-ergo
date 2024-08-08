(set-logic ALL)
(set-option :produce-models true)
(declare-const x Int)
(assert (! (= x 0) :named foo))
(check-sat)
(get-model)
; The next instruction should fail because we did not activate the option
(get-assignment)