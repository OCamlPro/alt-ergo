(set-logic ALL)
(set-option :produce-models true)

;; Constants
;; Bools
(declare-const b Bool)
(assert b)
(check-sat)

;; Ints
(declare-const i Int)
(assert (> i 0))
(check-sat)

;; Reals
(declare-const r Real)
(assert (> r 0.0))
(check-sat)

;; UF
;; Bools
(declare-const fb_cst Bool)
(declare-const fb_cst2 Bool)
(declare-fun fb (Bool) Bool)
(declare-fun fb_b (Bool Bool) Bool)
(assert (and (fb fb_cst) (fb_b fb_cst fb_cst2)))
(check-sat)

;; Ints
(declare-const fi_cst Int)
(declare-fun fi (Int) Bool)
(declare-fun fii (Int) Int)
(declare-fun fii_i (Int Int) Int)
(assert (and (fi fi_cst) (= (fii fi_cst) 0) (= (fii_i 1 2) fi_cst)))  
(check-sat)

;; Reals
(declare-const fr_cst Real)
(declare-fun fr (Real) Bool)
(declare-fun frr (Real) Real)
(declare-fun frr_r (Real Real) Real)
(assert (and (fr fr_cst) (= (frr fr_cst) 1.0) (= (frr_r 1.0 2.0) fr_cst)))
(check-sat)

;; Sorts
(declare-sort S0 0)
(declare-const sa S0)
(declare-const sb S0)
(assert (= sa sb))
(check-sat)

(declare-sort S1 1)
(declare-const s1a (S1 S0))
(declare-const s1b (S1 S0))
(assert (= s1a s1b))
(check-sat)

;; Arrays
(declare-const a (Array Int Int))
(assert (= a (store a 1 1)))
(assert (= (select a 1) 1))

(declare-const ai_cst Int)
(define-fun ai () (Array Int Int) (store a ai_cst 1))
(assert (= (select ai ai_cst) 1))
(check-sat)
(get-model)

;; Sums
(declare-datatype s ((A) (B) (C)))
(declare-const s_cst s)
(assert (or (= s_cst A) (= s_cst B)))
(check-sat)
(get-model)

;; Records
(declare-datatype r ((mk_r (r0 Int) (r1  Int))))
(declare-const r_cst r)
(assert (> (r0 r_cst) 1))
(check-sat)

(define-fun r_fun () r (mk_r 1 2))
(assert (= (r1 r_fun) 2))
(check-sat)
(get-model)

;; Adts
(declare-datatype IntList ((Cons (hd Int) (tl IntList)) (Nil)))
(declare-const l_cst IntList)
; not yet supported
;(assert (= (hd l_cst) 1))
;(assert (= l_cst Nil))
(check-sat)