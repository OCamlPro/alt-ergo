(set-logic QF_BV)

(assert (distinct ((_ zero_extend 2) #b01) (concat #b01 #b00)))
(check-sat)
(assert (distinct ((_ zero_extend 2) #b01) (concat #b00 #b01)))
(check-sat)
