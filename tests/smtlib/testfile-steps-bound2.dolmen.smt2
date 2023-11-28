(set-option :steps-bound 2)
(set-logic ALL)

(declare-const x Int)
(assert (= (* x x) 3))
; Should answer 'unknown'
(check-sat)
(get-info :reason-unknown)

(reset)

(set-option :steps-bound 100)
(set-logic ALL)
(declare-const x Int)
(assert (= (* x x) 3))
; Should answer 'unsat'
(check-sat)