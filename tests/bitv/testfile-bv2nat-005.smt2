(set-logic ALL)
(declare-const x (_ BitVec 1024))
(assert (distinct ((_ int2bv 512) (bv2nat x)) ((_ extract 511 0) x)))
(check-sat)
