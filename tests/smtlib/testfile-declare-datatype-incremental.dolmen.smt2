(set-logic ALL)
(push 1)
(declare-datatype t
  ((c1 (d1 Int)) (c2)))
(pop 1)
(declare-datatype t
  ((c2 (d1 Int)) (c1)))
(declare-const x t)
(declare-const y t)
(assert ((_ is c1) x))
(assert ((_ is c1) y))
(assert (distinct x y))
(check-sat)
