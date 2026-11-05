(set-logic ALL)
(declare-const i Int)
(assert
 (distinct (store ((as const (Array Int Int)) 0) i 0) ((as const (Array Int Int)) 0)))
(check-sat)
