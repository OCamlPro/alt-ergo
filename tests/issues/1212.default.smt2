; The generated model is incorrect. It should ensure that a and b are
; equal everywhere except on 0. This bug should be resolved
; after addressing https://github.com/OCamlPro/alt-ergo/issues/929

(set-option :produce-models true)
(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= (store a 0 0) (store b 0 0)))
(check-sat)
(get-model)
