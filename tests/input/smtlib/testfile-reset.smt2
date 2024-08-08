(set-logic ALL)

(declare-const b Bool)

(assert (and b (not b)))
(check-sat)
(reset)
(check-sat)