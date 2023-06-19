(set-logic QF_BV)
(assert (let ((?v_0 ((_ zero_extend 24) (_ bv0 8)))) (and (= ?v_0 (_ bv0 32)) (= (_ bv0 8) ((_ extract 7 0) (bvand ?v_0 (_ bv3 32) (_ bv1 32)))))))
(check-sat)

; expected sat
; Tableaux, Tableaux-CDCL -> unknown
; CDCL -> crash
; CDCL-Tableaux -> unknown
