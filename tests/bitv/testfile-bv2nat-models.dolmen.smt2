(set-logic ALL)
(set-option :produce-models true)
(declare-const x (_ BitVec 4))
(assert (= (bv2nat x) 7))
(check-sat)
(get-model)