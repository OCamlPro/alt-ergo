(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(declare-sort intref 0)
(declare-fun intrefqtmk (Int) intref)
(declare-fun a () Int)
(define-fun aqtunused () intref (intrefqtmk a))
(declare-fun a1 () Int)
(assert (not (and (<= 5 a1) (<= a1 15))))
(check-sat)
(get-model)
