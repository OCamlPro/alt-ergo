(set-logic ALL)
(assert (= ((as const (Array Int Int)) 0) ((as const (Array Int Int)) 1)))
(check-sat)
