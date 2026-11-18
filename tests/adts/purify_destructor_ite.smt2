; A destructor of a boolean field applied to an ite used to crash in
; purify_form.
(set-logic ALL)
(declare-datatype R ((mk (flag Bool) (val Int))))
(declare-const r R)
(declare-const s R)
(declare-const p Bool)
(assert (flag (ite p r s)))
(assert (not (flag r)))
(assert (not (flag s)))
(check-sat)
