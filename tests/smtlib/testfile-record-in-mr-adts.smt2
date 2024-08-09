(set-logic ALL)
(declare-datatypes ((u 0) (v 0)) (((Record)) ((C) (D))))
(define-fun a () u Record)
(check-sat)
