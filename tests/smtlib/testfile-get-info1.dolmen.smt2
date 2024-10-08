(set-logic ALL)

(declare-const x Int)

(assert (= (* x x) 4))

(check-sat)
(get-info :all-statistics)
(get-info :assertion-stack-levels)
(get-info :authors)
(get-info :error-behavior)
(get-info :name)
(get-info :reason-unknown)
(get-info :version)