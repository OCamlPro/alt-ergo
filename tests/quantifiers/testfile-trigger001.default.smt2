(set-logic ALL)
(declare-fun P (Int) Bool)
(declare-fun f (Int) Int)

; This quantifier is explicitly annotated with a (f x) trigger.
; It should not cause this problem to be unsat.
(assert
 (forall ((x Int))
  (! (not (P x)) :pattern ((f x)))))

; Note that we don't use (f 0).
(assert (P 0))

(check-sat)
