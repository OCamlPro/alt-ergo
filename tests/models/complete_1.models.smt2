(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
; The preprocessor will replace this equation by `true` but we still
; have to produce a model value for `x`.
(assert (= x x))
(check-sat)
(get-model)
