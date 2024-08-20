(set-logic ALL)
(declare-datatype t ((B (i Int))))

(declare-const e t)

(assert ((_ is B) e))
(assert (forall ((n Int)) (distinct e (B n))))
(check-sat)
