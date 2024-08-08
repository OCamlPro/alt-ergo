(set-logic ALL)
(declare-fun P (Int) Bool)
(declare-fun f (Int) Int)

; This quantifier is explicitly annotated with a (f x) trigger.
; It should cause this problem to be unsat.
(assert
 (forall ((x Int))
  (! (not (P x)) :pattern ((f x)))))

; Use (f 0)
(assert (= (f 0) 0))

(assert (P 0))

(check-sat)
