(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (= (f a) (f b)))
(check-sat)
(get-model)
