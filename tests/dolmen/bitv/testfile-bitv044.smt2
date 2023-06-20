(set-logic QF_BV)
(define-fun t () (_ BitVec 8) (_ bv0 8))
(assert (not (bvslt (concat t (_ bv0 24)) (_ bv0 32))))
(check-sat)
