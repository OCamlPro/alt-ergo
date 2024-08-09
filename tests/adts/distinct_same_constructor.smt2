(set-logic ALL)

(declare-datatype list
  ((cons (value Int) (tail list)) (nil)))

(declare-fun l () list)
(assert (distinct l (cons 0 nil) nil))
(check-sat)
(exit)
