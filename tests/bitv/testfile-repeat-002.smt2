(set-logic ALL)
(set-option :reproducible-resource-limit 100)
(declare-const x (_ BitVec 10))
; Previously, we would be creating a huge amount of terms here and timeout.
(assert (distinct ((_ extract 124 95) ((_ repeat 1024) x)) (concat (concat ((_ extract 4 0) x) ((_ repeat 2) x)) ((_ extract 9 5) x))))
(check-sat)
