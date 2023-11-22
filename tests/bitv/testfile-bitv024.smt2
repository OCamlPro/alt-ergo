(set-logic ALL)
(declare-const x (_ BitVec 4))
(assert (= (bv2nat ((_ extract 3 2) x)) 0))
(check-sat)
