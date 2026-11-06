(set-logic ALL)
(assert (= ((as ae.const (Array Int Int)) 0) ((as ae.const (Array Int Int)) 1)))
(check-sat)
