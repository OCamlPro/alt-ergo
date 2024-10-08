(set-logic ALL)
(set-option :produce-models true)
(declare-const f Int)
(assert (= f 0))
; This function is user-defined and shouldn't appear in the output model.
(define-fun g ((x Int) (y Int)) Int (+ x y))
(check-sat)
(get-model)
