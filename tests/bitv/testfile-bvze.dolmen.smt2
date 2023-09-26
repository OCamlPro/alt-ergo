(set-logic BV)

(push 1)
(assert (= ((_ zero_extend 8) #b11111111) #b1000000011111111))
(check-sat)
(pop 1)

(push 1)
(assert (= ((_ zero_extend 8) #b11111111) #b0000000011111111))
(check-sat)
(pop 1)

(push 1)
(assert (= ((_ zero_extend 0) #b11111111) #b11111111))
(check-sat)
(pop 1)