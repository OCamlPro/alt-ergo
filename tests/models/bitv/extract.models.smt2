(set-logic BV)
(set-option :produce-models true)

(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 3))
(declare-const c (_ BitVec 6))
(declare-const z (_ BitVec 1))

(assert (= ((_ extract 0 0) c) #b1))
(assert (= ((_ extract 5 5) c) #b1))
(assert (= (concat (concat b z) a) c))

(assert (= ((_ extract 1 1) a) #b1))
(assert (= ((_ extract 1 0) b) #b11))
(assert (= z #b0))

(check-sat)
(get-model)
