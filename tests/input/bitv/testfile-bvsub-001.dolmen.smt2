(set-logic ALL)
(declare-const x (_ BitVec 1024))
(declare-const y (_ BitVec 1024))
; Subtraction of low bits is independent of high bits
(assert (distinct ((_ extract 3 0) (bvsub (concat x #b0101) (concat y #b0111))) #b1110))
(check-sat)
