(set-logic ALL)

(set-option :produce-models true)
(declare-const x Real)
(assert (> x 0.0))
(assert (= ((_ ae.round 1 2) RTZ 0.3) x))
(check-sat)
(get-model)