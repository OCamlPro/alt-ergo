; The value of (select (store a i 1) j) is propagated to a at j: the term
; (select a j) must be in its class to match the pattern (f (select a x)).
(set-logic ALL)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-fun f (Int) Int)
(assert
 (forall ((x Int)) (! (= (f (select a x)) 0) :pattern ((f (select a x))))))
(assert (distinct i j))
(assert (distinct (f (select (store a i 1) j)) 0))
(check-sat)
