(set-logic QF_BV)

(assert (distinct ((_ rotate_right 4) #b11010110) #b11100110))
(check-sat)
(assert (distinct ((_ rotate_right 4) #b11010110) #b01101101))
(check-sat)
