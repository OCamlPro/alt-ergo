; The bounds of (to_int a) are propagated to a.
(set-logic ALL)
(declare-const a Real)
(assert (<= 15.0 a))
(assert (< a 15.5))
(assert (not (= (to_int a) 15)))
(check-sat)
