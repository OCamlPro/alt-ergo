(set-logic QF_BV)
(declare-const R (_ BitVec 1))
(set-info :status unsat)

(assert
  (=
    (_ bv1 1)
    (ite
      (=
        (_ bv1 4)
        (bvand
          (_ bv1 4)
          (bvlshr (_ bv0 4) ((_ zero_extend 3) R))))
      (_ bv1 1)
      (_ bv0 1))))

(check-sat)
