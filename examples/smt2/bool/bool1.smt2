(set-logic QF_UF)
(set-option :produce-models true) ; enable model generation
(declare-const p Bool)
(declare-const q Bool)
(assert (!(=> (not p) q) :named ass1))
(check-sat)
(get-model)
(exit)
