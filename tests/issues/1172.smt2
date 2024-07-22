(set-logic ALL)
(declare-datatype record ((mkrecord (field Int))))
(declare-const boxed record)
(define-fun add ((x Int) (y Int)) Int (+ x y))
(assert
 (distinct
  (* (field boxed) (add (field boxed) 1))
  (add (* (field boxed) (field boxed)) (field boxed))))
(check-sat)
