  $ alt-ergo 2>/dev/null << EOF
  > (set-logic QF_LIA)
  > (set-option :produce-models true)
  > (declare-const t Int)
  > (declare-const x Int)
  > (assert (and (> t (+ x 1)) (> 1 (+ 1 t x))))
  > (maximize x)
  > (check-sat)
  > (get-model)
  > (get-objectives)
  > EOF
  
  unknown
  (
    (define-fun x () Int (- 2))
    (define-fun t () Int 0)
  )
  (objectives 
    (x (- 2))
  )
