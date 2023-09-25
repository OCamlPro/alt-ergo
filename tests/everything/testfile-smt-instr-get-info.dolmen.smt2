(set-logic ALL)

(declare-const x Int)
(declare-const y Int)

(assert (= (* x x) 4))

(get-info :reason-unknown)
(check-sat)
(get-info :all-statistics)
(get-info :assertion-stack-levels)
(get-info :authors)
(get-info :error-behavior)
(get-info :name)
(get-info :reason-unknown)
(get-info :version)
(get-info :foo)