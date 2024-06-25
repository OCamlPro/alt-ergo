(set-logic ALL)
(declare-const x (_ BitVec 1024))

(assert (distinct ((_ int2bv 2048) (bv2nat x)) (concat (_ bv0 1024) x)))
(check-sat)
