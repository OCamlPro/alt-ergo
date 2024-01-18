(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
(declare-fun f (Int) Int)
; There is no constraint on `x` and `f` but we still have to produce a model
; value for them.
(check-sat)
(get-model)
