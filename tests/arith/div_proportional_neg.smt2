; (3 * x) div (2 * x) is 2 for x = -1: Alt-Ergo used to replace it by
; 3 div 2 = 1 regardless of the sign of x, and wrongly answered unsat.
(set-logic ALL)
(declare-const x Int)
(assert (< x 0))
(assert (not (= (div (* 3 x) (* 2 x)) 1)))
(check-sat)
