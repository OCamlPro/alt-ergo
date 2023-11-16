(set-logic ALL)

(declare-const x Int)
(declare-const y Int)
(assert (= (* x x) 3))

; Should answer 'unknown'
(push 1)
(set-option :steps-bound 2)
(check-sat)
(get-info :reason-unknown)
(pop 1)

(reset)

; Should answer 'unsat'
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(set-option :steps-bound 100)
(assert (= (* x x) 3))
(check-sat)