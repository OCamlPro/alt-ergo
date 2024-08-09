(set-logic ALL)

(declare-const x Real)
(assert (> x 0.0))
(assert (= ((_ ae.round 1 1) RTZ 0.3) x))
(check-sat)