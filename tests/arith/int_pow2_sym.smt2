(set-logic ALL)
(declare-const n Int)
(assert (not (= (int.pow2 n) (ae.pow_int 2 n))))
(check-sat)
