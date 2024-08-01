(set-logic ALL)
(set-option :reproducible-resource-limit 100)
(declare-const x (_ BitVec 1))
; Previously, we would be creating a huge amount of terms here and timeout.
(assert (distinct ((_ extract 1023 1023) ((_ sign_extend 1023) x)) x))
(check-sat)
