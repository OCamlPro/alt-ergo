(set-logic ALL)

(declare-const x Int)

(assert (= (* x x) 4))

(get-info :reason-unknown)
(check-sat)