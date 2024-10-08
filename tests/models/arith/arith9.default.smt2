; This test checks if the optimization doesn't stop after trying to
; optimize a strict bound.
(set-option :produce-models true)
(set-logic ALL)
(declare-const x Real)
(declare-const y Real)
; If the SAT solver explores first the right branch of the following OR gate, it
; shouldn't conclude that x cannot be optimized.
(assert (or (<= x 4.0) (< x 1.5)))
(maximize x)
; The current implementation of SatML explores the right branch of OR gates
; first. We add the following line to be sure the optimization feature still
; works after changing the order of branches.
(assert (or (< y 1.5) (<= y 4.0)))
(maximize y)
(check-sat)
(get-model)
(get-objectives)
