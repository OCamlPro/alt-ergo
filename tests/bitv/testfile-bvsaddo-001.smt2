(set-logic ALL)
(declare-const x (_ BitVec 1024))
(declare-const y (_ BitVec 1024))

(assert (bvsaddo x y))
(assert (= y (_ bv0 1024)))

(check-sat)
