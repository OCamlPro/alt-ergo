(set-logic ALL)

(declare-const x Real)

(push 1)

  ; This should be unknown, because the trigger does not apply
  (assert (not (my_leq (to_real (to_int x)) x)))
  (check-sat)

  ; Now we know that x > 10 and so the trigger should apply since 10 > 0
  ; Note that this also tests that [to_real] / [to_int] here are the same as
  ; [real_of_int] / [int_floor] in native syntax
  (assert (> x 10))
  (check-sat)

(pop 1)

(push 1)

  ; This should be unknown, because the trigger does not apply
  (assert (not (my_leq (f x) x)))
  (check-sat)

  ; Now that x > 10 is known, the trigger should apply
  (assert (> x 10))
  (check-sat)

(pop 1)
