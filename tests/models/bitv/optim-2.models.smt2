; Test primitive optimization
(set-option :produce-models true)
(set-option :verify-models false)
(set-logic ALL)
(declare-const x (_ BitVec 32))
(minimize (bvnot x))
(check-sat)
(get-model)
(get-objectives)
