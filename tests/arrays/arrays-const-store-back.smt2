(set-logic ALL)
(declare-const i Int)
(assert
 (distinct
  (store (store ((as ae.const (Array Int Int)) 0) i 1) i 0)
  ((as ae.const (Array Int Int)) 0)))
(check-sat)
