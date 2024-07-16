; Test basic functionality
(set-logic ALL)
(set-option :produce-models true)
(declare-const x (_ BitVec 32))
(maximize x)
(check-sat)
(get-model)
(get-objectives)
