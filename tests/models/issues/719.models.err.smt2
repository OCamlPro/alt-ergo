(set-logic ALL)
(set-option :produce-models true)
(declare-const a (Array Int Int))
(declare-const s Int)
(assert (and (<= 0 s) (<= s 10)))
(assert (forall ((k Int)) (=> (and (<= 0 k) (< k s)) (<= (select a k) (select a s)))))
(assert (forall ((k Int)) (=> (and (< s k) (<= k 10)) (<= (select a s) (select a k)))))
(assert (
  forall ((p Int) (q Int))
    (=> (and (<= 0 p) (< p q) (<= q (- s 1))) (<= (select a p) (select a q)))))
(assert (
  forall ((p Int) (q Int))
    (=> (and (<= (+ s 1) p) (< p q) (<= q 10)) (<= (select a p) (select a q)))))
(assert (not (
  forall ((p Int) (q Int))
    (=> (and (<= 0 p) (< p q) (<= q 10)) (<= (select a p) (select a q))))))
(check-sat)
(get-model)
; (get-model) should fail because the problem is UNSAT.