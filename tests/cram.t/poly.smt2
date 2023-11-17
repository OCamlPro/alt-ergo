(set-logic ALL)
(set-info :smt-lib-version 2.6)

(declare-sort list 1)

(declare-fun cons (par (a) (a (list a)) (list a)))
(declare-fun nil (par (a) () (list a)))

(define-fun singleton (par (a) ((x a)) (list a) (cons x nil)))

(assert (par (a) (exists ((x a)) (not (= nil (singleton x))))))

(assert (forall ((x Int)) (not (= nil (singleton x)))))

(assert (par (a) (forall ((x a)) (not (= nil (singleton x))))))

(declare-sort s 0)
(declare-fun foo () s)

(assert (not (= nil (singleton foo))))
(assert (not (= nil (singleton 1))))

(check-sat)
(get-value ((as nil (list Int)) (singleton 1) (as nil (list s)) (singleton foo)))
(get-model)
