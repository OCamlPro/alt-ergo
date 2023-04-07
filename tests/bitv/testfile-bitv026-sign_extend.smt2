(set-logic QF_BV)

(assert (distinct ((_ sign_extend 2) #b10) (concat #b00 #b10)))
(check-sat)
(assert (distinct ((_ sign_extend 2) #b10) (concat #b11 #b10)))
(check-sat)
