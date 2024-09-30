(set-logic ALL)

(declare-const x Int)
(assert (= (* x x) 3))
(set-option :steps-bound 2)
; Should fail because this option cannot be set after set-logic
(check-sat)