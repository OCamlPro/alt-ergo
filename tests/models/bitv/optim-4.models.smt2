; Test constrained function optimization
(set-logic ALL)
(set-option :produce-models true)
(declare-const x (_ BitVec 32))
(define-fun bvabs32 ((x (_ BitVec 32))) (_ BitVec 33)
  (ite
    (= ((_ extract 31 31) x) #b1)
    (concat #b0 x)
    (concat #b1 x)))
(maximize (bvabs32 x))
(assert (bvslt x (_ bv0 32)))
(check-sat)
(get-model)
(get-objectives)
