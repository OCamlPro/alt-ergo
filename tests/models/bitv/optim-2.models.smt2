; Test primitive optimization
(set-logic ALL)
(set-option :produce-models true)
(declare-const x (_ BitVec 32))
(minimize (bvnot x))
(check-sat)
(get-model)
(get-objectives)
