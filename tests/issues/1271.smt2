; Test printing of negative real values
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Real)
(assert (= x (- 42.0)))
(check-sat)
(get-model)
