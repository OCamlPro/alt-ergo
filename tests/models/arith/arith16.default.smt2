; Model generation used to assign x * x and y * y before x and y, after which
; the search for values of x and y did not terminate.
(set-option :produce-models true)
(set-logic ALL)
(declare-const x Real)
(declare-const y Real)
(assert (<= 3.0 (+ (* x x) (* y y))))
(assert (<= (+ (* x x) (* y y)) 5.0))
(check-sat)
(get-model)
