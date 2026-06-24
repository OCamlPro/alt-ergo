Testing Alt-Ergo's support for parsing smt-lib FPA literals.

  $ alt-ergo -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ +oo 8 24) (fp #b0 #b11111111 #b00000000000000000000000))
  >     (= (_ +oo 8 24) ((_ to_fp 8 24) #b01111111100000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ -oo 8 24) (fp #b1 #b11111111 #b00000000000000000000000))
  >     (= (_ -oo 8 24) ((_ to_fp 8 24) #b11111111100000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ +zero 8 24) (fp #b0 #b00000000 #b00000000000000000000000))
  >     (= (_ +zero 8 24) ((_ to_fp 8 24) #b00000000000000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat
  $ alt-ergo -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ -zero 8 24) (fp #b1 #b00000000 #b00000000000000000000000))
  >     (= (_ -zero 8 24) ((_ to_fp 8 24) #b10000000000000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat
  $ alt-ergo -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (= (_ NaN 8 24) (_ NaN 8 24))))
  > (check-sat)
  > EOF
  
  unsat
  $ alt-ergo -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (= (fp #b0 #b01111111 #b00000000000000000000000)
  >                ((_ to_fp 8 24) #b00111111100000000000000000000000))))
  > (check-sat)
  > EOF
  
  unsat

Testing Alt-Ergo's symbolic reasoning over smt-lib FPA symbols.
  $ alt-ergo -t 1 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isPositive x))
  > (assert (fp.isNegative x))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 1 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isNegative (fp.abs x)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 1 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.isZero x))
  > (assert (fp.isZero y))
  > (assert (fp.isInfinite (fp.add roundNearestTiesToEven x y)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 1 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.isZero x))
  > (assert (fp.isZero y))
  > (assert (fp.lt x y))
  > (assert (fp.leq y x))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 1 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (declare-const z (_ FloatingPoint 8 24))
  > (assert (fp.isZero x))
  > (assert (fp.isZero y))
  > (assert (fp.isZero z))
  > (assert (fp.lt (fp.fma roundNearestTiesToEven x y z) z))
  > (check-sat)
  > EOF
  
  unsat

