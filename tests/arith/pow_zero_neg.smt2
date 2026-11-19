; 0 to a negative power is undefined, so y can be 5. Alt-Ergo used to fold it
; to the infinite rational 1/0 and answered unsat.
(set-logic ALL)
(set-option :produce-models true)
(declare-const x Real)
(declare-const y Real)
(assert (= x 0.0))
(assert (= y (ae.pow_real x (- 1.0))))
(assert (= y 5.0))
(check-sat)
(get-model)
