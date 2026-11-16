  $ alt-ergo << EOF
  > (set-logic QF_LIA)
  > (set-option :produce-models true)
  > (declare-const t Int)
  > (declare-const x Int)
  > (assert (and (> t (+ x 1)) (> 1 (+ 1 t x))))
  > (maximize x)
  > (check-sat)
  > (get-model)
  > (get-objectives)
  > EOF
  Fatal error: exception File "src/lib/util/numbers.ml", line 214, characters 4-10: Assertion failed
  [2]
