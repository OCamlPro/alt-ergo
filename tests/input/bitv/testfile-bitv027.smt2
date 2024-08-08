(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
; This used to crash
(assert (= (concat #b00000000 (concat x (concat ((_ extract 6 5) x) ((_ extract 3 1) x)))) (concat y (concat y (concat #b00 ((_ extract 6 4) x)))
)))
(check-sat)
