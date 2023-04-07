
(set-logic QF_BV)

(assert (distinct ((_ repeat 3) #b01) (concat #b01 #b1101)))
(check-sat)
(assert (distinct ((_ repeat 3) #b01) (concat #b01 #b0101)))
(check-sat)
