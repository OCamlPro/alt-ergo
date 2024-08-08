(set-logic ALL)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
; This forces the values of x and y to all ones
(assert (= x (bvor #b10100101 y)))
(assert (= y (bvor #b01011010 x)))
(check-sat)
(get-model)
