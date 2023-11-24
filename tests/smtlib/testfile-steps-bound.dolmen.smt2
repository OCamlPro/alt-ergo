(set-logic ALL)

(declare-const x Int)
(declare-const y Int)
(assert (= (* x x) 3))

(push 1)
; Setting this option here should fail because the previous assertion takes
; more than 2 steps. It does not because AE does not execute SMTLIB instruction
; imperatively; here, the option is actually set before the assertion is
; executed.
(set-option :steps-bound 2)
; Should answer 'unknown'
(check-sat)
(get-info :reason-unknown)
(pop 1)

(reset)

(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(set-option :steps-bound 100)
; Should answer 'unsat'
(assert (= (* x x) 3))
(check-sat)