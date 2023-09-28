(set-logic ALL)

; Pushing an empty assertion stack
(push 1)
(check-sat)

(declare-const x Int)
; Pushing twice the assertion stack with 'x'
(push 2)

; Pushing once the assertion stack with 'y'
(declare-const y Int)
(push 1)

(assert (= x y))
(check-sat)

; Popping three times -> y disappears
(pop 3)

(assert (= x y))
; Raises an error