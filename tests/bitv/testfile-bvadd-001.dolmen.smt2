(set-logic ALL)
(declare-const x (_ BitVec 1024))
(declare-const y (_ BitVec 1024))
; Addition of low bits is independent from high bits
(assert (distinct ((_ extract 3 0) (bvadd (concat x #b0101) (concat y #b1100))) #b0001))
(check-sat)
