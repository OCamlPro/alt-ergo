(set-logic ALL)

(declare-const x Int)

(push 1)
(assert (> x 0))
(push 1)
(pop 1)
(pop 1)
(assert (< x 0))
(check-sat)
