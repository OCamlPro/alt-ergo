(set-logic ALL)

(declare-const x Int)
(declare-const b Bool)

(assert (<= 2 x))
(assert (<= x (ite b 2 (div 1 x))))

(check-sat)
