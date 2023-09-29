(set-logic BV)
(set-option :produce-models true)

(declare-const x (_ BitVec 2))
(assert (= (bvnot x) #b00))
(assert (= x #b00))
(check-sat)
