; Model generation used to loop forever, bisecting a towards [0, 1) after
; choosing y = 0.
(set-logic ALL)
(set-option :produce-models true)
(declare-const y Int)
(declare-const a Real)
(assert (= y (to_int a)))
(assert (> a 2.5))
(check-sat)
(get-model)
