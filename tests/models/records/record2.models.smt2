(set-logic ALL)
(set-option :produce-models true)
(declare-datatype Pair
((pair (first Int) (second Int))))
(declare-fun f (Int) Pair)
(assert (= (first (f 0)) 5))
(check-sat)
(get-model)
