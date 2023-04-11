(set-logic QF_BV)

(assert (distinct (bvneg #b0110) #b1011))
(check-sat)
(assert (distinct (bvneg #b0110) #b1010))
(check-sat)
