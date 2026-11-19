; (3 * x) div (2 * x) is 1 when x > 0 (and 2 when x < 0): when the sign of the
; divisor is known, the quotient of proportional polynomials is computed.
(set-logic ALL)
(declare-const x Int)
(assert (> x 0))
(assert (not (= (div (* 3 x) (* 2 x)) 1)))
(check-sat)
