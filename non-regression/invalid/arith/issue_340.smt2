(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun p (Int Int Int Int) Bool)

(assert (p a b c d)) ; just here for ordering of variables
(assert (<= a 0))
(assert (>= c 0))
(assert (>= b 0))
(assert (>= (+ (* (- 4) c) (* (- 2) b) a 1) 0))
(check-sat)
