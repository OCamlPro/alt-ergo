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
; https://github.com/OCamlPro/alt-ergo/issues/1163
(declare-fun P ((_ BitVec 33)) Bool)
(assert (P (bvabs32 x)))
(check-sat)
(get-model)
(get-objectives)
