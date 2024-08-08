(set-logic ALL)
(declare-datatype t ((Record)))
(define-fun a () t Record)
(check-sat)
