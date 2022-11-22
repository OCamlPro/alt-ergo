(declare-fun h () (Array Int (Array Int Real)))

(assert (forall ((x1 Int) (x2 Int) (aar1 (Array Int (Array Int Real))) (aar2 (Array Int (Array Int Real)))) 
        (or (not (= (select (select aar1 x1) x2) (select (select aar1 x2) x1))) (not (= (select (select aar2 x1) x2) (select (select aar2 x2) x1))))))

(assert (not  
        (= (select (select h 0) 1) (select (select h 1) 0))))

(check-sat)
(exit)
