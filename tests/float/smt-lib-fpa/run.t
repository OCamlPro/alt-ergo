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

  $ alt-ergo -t 1 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (=
  >   (_ +oo 11 53)
  >   (fp.fma roundNearestTiesToEven
  >     (fp (_ bv1 1) (_ bv1 11) (_ bv0 52))
  >     (fp (_ bv1 1) (_ bv2047 11) (_ bv0 52))
  >     (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))
  >   )
  > )))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 1 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-fun x () Float64)
  > (declare-fun y () Float64)
  > (assert (= x (fp (_ bv0 1) #b10011100010 (_ bv0 52))))
  > (assert (= y (fp (_ bv1 1) #b11111000100 (_ bv0 52))))
  > (assert (not (= (_ -oo 11 53) (fp.mul roundNearestTiesToEven x y))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 1 --timelimit-per-goal -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-fun x () Float64)
  > (declare-fun y () Float64)
  > (declare-fun r () Float64)
  > (assert (= x (fp #b1 #b01011000011 #b1101000000101001011111101100101000101111000010110111)))
  > (assert (= y (fp #b1 #b11011011000 #b1110011100101011100011010111111001100001011001000011)))
  > (assert (= r (fp #b0 #b11011011000 #b1110011100101011100011010111111001100001011001000011)))
  > (assert (= (fp.sub roundTowardPositive x y) r))
  > (check-sat)
  > EOF
  
  unknown

An overflow of to_fp from a real gives the largest finite float with RTZ (and
RTN/RTP towards zero), infinity otherwise.

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (> r 10000000000000000000000000000000000000000.0))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) RTZ r))))
  > (check-sat)
  > EOF
  
  unknown

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (> r 10000000000000000000000000000000000000000.0))
  > (assert (fp.isInfinite ((_ to_fp 8 24) RTZ r)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (< r (- 10000000000000000000000000000000000000000.0)))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) RTN r))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (> r 10000000000000000000000000000000000000000.0))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) RNE r))))
  > (check-sat)
  > EOF
  
  unsat

The largest finite value of Float(3,5) is 15.5, not an integer: RTP rounds -18
to -15.5, so this is satisfiable and must not be unsat.

  $ alt-ergo --steps-bound 1000 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (= r (- 18.0)))
  > (assert (not (fp.eq ((_ to_fp 3 5) RTP r) (fp #b1 #b110 #b1100))))
  > (check-sat)
  > EOF
  
  unknown

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (= r (- 18.0)))
  > (assert (not (fp.eq ((_ to_fp 3 5) RTP r) (fp #b1 #b110 #b1111))))
  > (check-sat)
  > EOF
  
  unsat

Quantified FP problems.

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic UFFP)
  > (declare-fun f ((_ FloatingPoint 8 24)) (_ FloatingPoint 8 24))
  > (assert (forall ((x (_ FloatingPoint 8 24)))
  >   (! (=> (fp.isInfinite x) (fp.isNaN (f x))) :pattern ((f x)))))
  > (assert (fp.eq (f (_ +oo 8 24)) (f (_ +oo 8 24))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic UFFPLRA)
  > (declare-fun g (Real) (_ FloatingPoint 8 24))
  > (assert (forall ((r Real)) (= (g r) ((_ to_fp 8 24) RNE r))))
  > (assert (not (fp.eq (g 1.0) ((_ to_fp 8 24) RNE 1.0))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic FP)
  > (assert (exists ((x (_ FloatingPoint 8 24))) (and (fp.isNaN x) (fp.isZero x))))
  > (check-sat)
  > EOF
  
  unsat

is_normal and is_subnormal are exclusive, one of the five properties always 
holds, and definition by the real value.

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isNormal x))
  > (assert (fp.isSubnormal x))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (not (fp.isNaN x)))
  > (assert (not (fp.isInfinite x)))
  > (assert (not (fp.isZero x)))
  > (assert (not (fp.isNormal x)))
  > (assert (not (fp.isSubnormal x)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isSubnormal x))
  > (assert (fp.gt x ((_ to_fp 8 24) RNE 0.5)))
  > (check-sat)
  > EOF
  
  unsat

isNormal/isSubnormal of the smallest and largest literals in (2, 3), (3, 5), 
Float16 and Float32

  $ alt-ergo -t 2 -o smtlib2 --enable-theory smt.float 2>/dev/null <<EOF
  > (set-logic ALL)
  > (define-fun cls () Bool (and
  >   (fp.isSubnormal (fp #b0 #b00 #b01)) 
  >   (fp.isSubnormal (fp #b1 #b00 #b11))
  >   (fp.isNormal (fp #b0 #b01 #b00)) 
  >   (fp.isNormal (fp #b1 #b10 #b11))
  >   (fp.isSubnormal (fp #b0 #b000 #b0001))
  >   (fp.isSubnormal (fp #b1 #b000 #b1111))
  >   (fp.isNormal (fp #b0 #b001 #b0000))
  >   (not (fp.isNormal (fp #b0 #b000 #b1111)))
  >   (fp.isSubnormal (fp #b0 #b00000 #b0000000001))
  >   (fp.isSubnormal (fp #b1 #b00000 #b1111111111))
  >   (fp.isNormal (fp #b0 #b00001 #b0000000000))
  >   (not (fp.isSubnormal (fp #b0 #b00001 #b0000000000)))
  >   (fp.isSubnormal ((_ to_fp 8 24) #x00000001))
  >   (fp.isSubnormal ((_ to_fp 8 24) #x807fffff))
  >   (fp.isNormal ((_ to_fp 8 24) #x00800000))
  >   (fp.isNormal ((_ to_fp 8 24) #xff7fffff))
  >   (not (fp.isNormal (_ +zero 8 24))) 
  >   (not (fp.isSubnormal (_ -zero 8 24)))
  >   (not (fp.isNormal (_ +oo 3 5))) 
  >   (not (fp.isSubnormal (_ NaN 2 3)))))
  > (push 1)
  > (assert (not cls))
  > (check-sat)
  > (pop 1)
  > (assert cls)
  > (check-sat)
  > EOF
  
  unsat
  
  unknown
