(set-logic ALL)
(declare-const x (_ BitVec 2))
(assert (or (< (bv2nat x) 0) (<= 4 (bv2nat x))))
(check-sat)
