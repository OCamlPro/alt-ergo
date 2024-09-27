; This test checks if the optimization doesn't stop after getting an optimized
; model in a fixed branch of the SAT solver.
(set-option :produce-models true)
(set-option :verify-models false)
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
; If the SAT solver explores first the right branch of the following OR gate, it
; shouldn't conclude that x = 2 is an optimized model.
(assert (or (<= x 4) (<= x 2)))
(maximize x)
; The current implementation of SatML explores the right branch of OR gates
; first. We add the following line to be sure the optimization feature still
; works after changing the order of branches.
(assert (or (<= y 2) (<= y 4)))
(maximize y)
(check-sat)
(get-model)
(get-objectives)
