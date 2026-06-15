(set-logic QF_FP)
(set-option :smt-lib-fpa true)

(push 1)
(assert (not (= (_ +oo 8 24) (fp #b0 #b11111111 #b00000000000000000000000))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= (_ -oo 8 24) (fp #b1 #b11111111 #b00000000000000000000000))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= (_ +zero 8 24) (fp #b0 #b00000000 #b00000000000000000000000))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= (_ -zero 8 24) (fp #b1 #b00000000 #b00000000000000000000000))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= (_ NaN 8 24) (_ NaN 8 24))))
(check-sat)
(pop 1)

