(set-logic QF_BV)
(define-fun a () (_ BitVec 4) (_ bv0 4))
(assert (not (bvslt a (_ bv0 4))))
(check-sat)
