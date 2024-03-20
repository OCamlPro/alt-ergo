(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
(push 1)
(declare-fun f (Int) Int)
(assert (= (f 0) 1))
(pop 1)
; The function `f` isn't declared anymore in the current context and we must
; not produce a model value for it.
(check-sat)
(get-model)
