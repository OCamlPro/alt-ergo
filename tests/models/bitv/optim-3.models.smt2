; Test constrained optimization
(set-logic ALL)
(set-option :produce-models true)
(declare-const x (_ BitVec 32))
(maximize x)
(assert (bvslt x ((_ int2bv 32) (- 1))))
(check-sat)
(get-model)
(get-objectives)
