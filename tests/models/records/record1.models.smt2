(set-logic ALL)
(set-option :produce-models true)
(declare-datatype Pair
((pair (first Int) (second Int))))
(declare-const a Pair)
(assert (= (first a) 5))
(check-sat)
(get-model)
