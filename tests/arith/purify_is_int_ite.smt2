; An interpreted predicate applied to an ite used to crash in purify_form.
(set-logic ALL)
(declare-const x Int)
(declare-const a Real)
(assert (is_int (ite (< x 0) a 1.5)))
(assert (>= x 0))
(check-sat)
