(set-logic QF_UF)
(set-option :produce-models true) ; enable model generation
(set-option :produce-assignments true) ; enable get assignment
(declare-const p Bool)
(declare-const q Bool)
; (declare-const t Int)
(define-fun nq () Bool q)
(assert (=> (! (not p) :named notp) (! (not nq) :named notnq)))
(check-sat)
(get-model)
(get-assignment)
(assert q)
(check-sat)
(get-model)
(get-assignment)
(exit)
