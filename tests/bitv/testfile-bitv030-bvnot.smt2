(set-logic QF_BV)

(assert (distinct (bvnot #b0101) #b0101))
(check-sat)
(assert (distinct (bvnot #b0101) #b1010))
(check-sat)
