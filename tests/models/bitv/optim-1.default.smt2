; Test basic functionality
(set-option :produce-models true)
(set-option :verify-models false)
(set-logic ALL)
(declare-const x (_ BitVec 32))
(maximize x)
(check-sat)
(get-model)
(get-objectives)
