(set-logic ALL)
(declare-const x (_ BitVec 1024))

(assert (= ((_ extract 1023 1023) x) #b0))
(assert (distinct (sbv_to_int x) (ubv_to_int x)))

(check-sat)
