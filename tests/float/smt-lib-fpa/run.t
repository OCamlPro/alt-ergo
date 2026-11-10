Testing Alt-Ergo's support for parsing smt-lib FPA literals.

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ +oo 8 24) (fp #b0 #b11111111 #b00000000000000000000000))
  >     (= (_ +oo 8 24) ((_ to_fp 8 24) #b01111111100000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ -oo 8 24) (fp #b1 #b11111111 #b00000000000000000000000))
  >     (= (_ -oo 8 24) ((_ to_fp 8 24) #b11111111100000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ +zero 8 24) (fp #b0 #b00000000 #b00000000000000000000000))
  >     (= (_ +zero 8 24) ((_ to_fp 8 24) #b00000000000000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat
  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (or
  >     (= (_ -zero 8 24) (fp #b1 #b00000000 #b00000000000000000000000))
  >     (= (_ -zero 8 24) ((_ to_fp 8 24) #b10000000000000000000000000000000))
  > )))
  > (check-sat)
  > EOF
  
  unsat
  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (= (_ NaN 8 24) (_ NaN 8 24))))
  > (check-sat)
  > EOF
  
  unsat
  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (assert (not (= (fp #b0 #b01111111 #b00000000000000000000000)
  >                ((_ to_fp 8 24) #b00111111100000000000000000000000))))
  > (check-sat)
  > EOF
  
  unsat

Testing Alt-Ergo's symbolic reasoning over smt-lib FPA symbols.
  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isPositive x))
  > (assert (fp.isNegative x))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isNegative (fp.abs x)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.isZero x))
  > (assert (fp.isZero y))
  > (assert (fp.isInfinite (fp.add roundNearestTiesToEven x y)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
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

  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
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

  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
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

  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-fun x () Float64)
  > (declare-fun y () Float64)
  > (assert (= x (fp (_ bv0 1) #b10011100010 (_ bv0 52))))
  > (assert (= y (fp (_ bv1 1) #b11111000100 (_ bv0 52))))
  > (assert (not (= (_ -oo 11 53) (fp.mul roundNearestTiesToEven x y))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 1000 -o smtlib2 2>/dev/null <<EOF
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

Conversions of literals: to_fp_unsigned, fp.to_sbv and FP -> FP overflow.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (= ((_ to_fp_unsigned 8 24) RNE #x05) ((_ to_fp 8 24) #x40a00000))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (= ((_ fp.to_sbv 8) RTZ ((_ to_fp 8 24) #xc0b00000)) #xfb)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (= ((_ to_fp 5 11) RNE ((_ to_fp 8 24) #x47800000)) (_ +oo 5 11))))
  > (check-sat)
  > EOF
  
  unsat

fp applied to symbolic bit-vectors, evaluated once they are known.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s (_ BitVec 1))
  > (declare-const e (_ BitVec 8))
  > (declare-const m (_ BitVec 23))
  > (assert (not (= (fp s e m) ((_ to_fp 8 24) #x3f800000))))
  > (assert (= s #b0))
  > (assert (= e #b01111111))
  > (assert (= m #b00000000000000000000000))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 32))
  > (assert (= b #x7f800000))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) b))))
  > (check-sat)
  > EOF
  
  unsat

to_fp of a real, evaluated once its argument is known, then converted.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (= x ((_ to_fp 8 24) RNE 1.5)))
  > (assert (not (= ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) RNE 1.5))))
  > (check-sat)
  > EOF
  
  unsat


An overflow of to_fp from a real gives the largest finite float with RTZ (and
RTN/RTP towards zero), infinity otherwise.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (> r 10000000000000000000000000000000000000000.0))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) RTZ r))))
  > (check-sat)
  > EOF
  
  unknown

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (> r 10000000000000000000000000000000000000000.0))
  > (assert (fp.isInfinite ((_ to_fp 8 24) RTZ r)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (< r (- 10000000000000000000000000000000000000000.0)))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) RTN r))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (> r 10000000000000000000000000000000000000000.0))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) RNE r))))
  > (check-sat)
  > EOF
  
  unsat

The largest finite value of Float(3,5) is 15.5, not an integer: RTP rounds -18
to -15.5, so this is satisfiable and must not be unsat.

  $ alt-ergo --steps-bound 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (= r (- 18.0)))
  > (assert (not (fp.eq ((_ to_fp 3 5) RTP r) (fp #b1 #b110 #b1100))))
  > (check-sat)
  > EOF
  
  unknown

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (= r (- 18.0)))
  > (assert (not (fp.eq ((_ to_fp 3 5) RTP r) (fp #b1 #b110 #b1111))))
  > (check-sat)
  > EOF
  
  unsat

Quantified FP problems.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic UFFP)
  > (declare-fun f ((_ FloatingPoint 8 24)) (_ FloatingPoint 8 24))
  > (assert (forall ((x (_ FloatingPoint 8 24)))
  >   (! (=> (fp.isInfinite x) (fp.isNaN (f x))) :pattern ((f x)))))
  > (assert (fp.eq (f (_ +oo 8 24)) (f (_ +oo 8 24))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic UFFPLRA)
  > (declare-fun g (Real) (_ FloatingPoint 8 24))
  > (assert (forall ((r Real)) (= (g r) ((_ to_fp 8 24) RNE r))))
  > (assert (not (fp.eq (g 1.0) ((_ to_fp 8 24) RNE 1.0))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic FP)
  > (assert (exists ((x (_ FloatingPoint 8 24))) (and (fp.isNaN x) (fp.isZero x))))
  > (check-sat)
  > EOF
  
  unsat

is_normal and is_subnormal are exclusive, one of the five properties always 
holds, and definition by the real value.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isNormal x))
  > (assert (fp.isSubnormal x))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
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

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (fp.isSubnormal x))
  > (assert (fp.gt x ((_ to_fp 8 24) RNE 0.5)))
  > (check-sat)
  > EOF
  
  unsat

isNormal/isSubnormal of the smallest and largest literals in (2, 3), (3, 5), 
Float16 and Float32

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
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

Classification of fp from its exponent and sign.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s (_ BitVec 1))
  > (declare-const e (_ BitVec 8))
  > (declare-const m (_ BitVec 23))
  > (assert (= e #b11111111))
  > (assert (fp.isZero (fp s e m)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s (_ BitVec 1))
  > (declare-const e (_ BitVec 8))
  > (declare-const m (_ BitVec 23))
  > (assert (= s #b1))
  > (assert (= e #b00000001))
  > (assert (fp.isPositive (fp s e m)))
  > (check-sat)
  > EOF
  
  unsat

Bits of fp deduced from its value.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s (_ BitVec 1))
  > (declare-const e (_ BitVec 8))
  > (declare-const m (_ BitVec 23))
  > (assert (= (fp s e m) (_ +oo 8 24)))
  > (assert (not (= e #b11111111)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s (_ BitVec 1))
  > (declare-const e (_ BitVec 8))
  > (declare-const m (_ BitVec 23))
  > (assert (fp.isNaN (fp s e m)))
  > (assert (= m #b00000000000000000000000))
  > (check-sat)
  > EOF
  
  unsat

The real value of fp is linear in its significand, which is not enumerated.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --sat-solver Tableaux 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s (_ BitVec 1))
  > (declare-const m (_ BitVec 23))
  > (assert (fp.gt (fp s #x7f m) ((_ to_fp 8 24) RNE 1.5)))
  > (assert (bvult m #b00100000000000000000000))
  > (check-sat)
  > EOF
  
  unsat

Injectivity of fp on non-NaN values.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s1 (_ BitVec 1))
  > (declare-const e1 (_ BitVec 8))
  > (declare-const m1 (_ BitVec 23))
  > (declare-const s2 (_ BitVec 1))
  > (declare-const e2 (_ BitVec 8))
  > (declare-const m2 (_ BitVec 23))
  > (assert (= (fp s1 e1 m1) (fp s2 e2 m2)))
  > (assert (= e1 #b00000001))
  > (assert (not (= m1 m2)))
  > (check-sat)
  > EOF
  
  unsat

BV -> FP conversions of symbolic bit-vectors.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 8))
  > (assert (not (= ((_ to_fp_unsigned 8 24) RNE b) ((_ to_fp 8 24) #x40a00000))))
  > (assert (= b #x05))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 8))
  > (assert (not (= ((_ to_fp 8 24) RNE b) ((_ to_fp 8 24) #xc0a00000))))
  > (assert (= b #xfb))
  > (check-sat)
  > EOF
  
  unsat

FP -> BV conversions of symbolic floats.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (not (= ((_ fp.to_ubv 8) RNE x) #x05)))
  > (assert (= x ((_ to_fp 8 24) #x40a00000)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (not (= ((_ fp.to_sbv 8) RTZ x) #xfb)))
  > (assert (= x ((_ to_fp 8 24) #xc0a00000)))
  > (check-sat)
  > EOF
  
  unsat

The result of fp.to_ubv is unspecified on NaN: this must not be unsat.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (fp.isNaN x))
  > (assert (= ((_ fp.to_ubv 8) RNE x) #x05))
  > (check-sat)
  > EOF
  
  unknown

FP -> FP conversion of symbolic floats.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (fp.isNaN x))
  > (assert (not (fp.isNaN ((_ to_fp 11 53) RNE x))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (fp.isInfinite x))
  > (assert (fp.isNegative x))
  > (assert (not (= ((_ to_fp 11 53) RNE x) (_ -oo 11 53))))
  > (check-sat)
  > EOF
  
  unsat

Functional consistency of fp.to_ubv, including where it is unspecified.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const y Float32)
  > (assert (fp.isNaN x))
  > (assert (= ((_ fp.to_ubv 8) RNE x) #x05))
  > (assert (= ((_ fp.to_ubv 8) RNE y) #x06))
  > (assert (= x y))
  > (check-sat)
  > EOF
  
  unsat

Symbolic FP -> FP conversions: NaN and the sign are preserved both ways.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (fp.isNaN ((_ to_fp 5 11) m x)))
  > (assert (not (fp.isNaN x)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (fp.isNegative x))
  > (assert (fp.isPositive ((_ to_fp 5 11) m x)))
  > (check-sat)
  > EOF
  
  unsat

A conversion to a wider format is exact: no overflow, and the same real value.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (fp.isInfinite ((_ to_fp 11 53) m x)))
  > (assert (not (fp.isInfinite x)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (fp.isNormal x))
  > (assert (not (= (fp.to_real ((_ to_fp 11 53) m x)) (fp.to_real x))))
  > (check-sat)
  > EOF
  
  unsat

A narrowing conversion is bounded by the rounding of the real value.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (fp.lt ((_ to_fp 8 24) RNE 1.0) x))
  > (assert (fp.lt x ((_ to_fp 8 24) RNE 2.0)))
  > (assert (fp.lt ((_ to_fp 5 11) RNE x) ((_ to_fp 5 11) RNE 0.5)))
  > (check-sat)
  > EOF
  
  unsat

A conversion to the same format is the identity.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (not (= x ((_ to_fp 8 24) m x))))
  > (check-sat)
  > EOF
  
  unsat

A narrowing conversion can underflow or overflow: these must not be unsat.

  $ alt-ergo --steps-bound 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (fp.isZero ((_ to_fp 5 11) m x)))
  > (assert (not (fp.isZero x)))
  > (check-sat)
  > EOF
  
  unknown

  $ alt-ergo --steps-bound 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const m RoundingMode)
  > (assert (not (fp.isInfinite x)))
  > (assert (fp.isInfinite ((_ to_fp 5 11) m x)))
  > (check-sat)
  > EOF
  
  unknown

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (declare-const r Real)
  > (assert (= r (- 3.5)))
  > (assert (= x ((_ to_fp 8 24) RNE r)))
  > (assert (not (= ((_ fp.to_sbv 8) RNE x) #xfc)))
  > (check-sat)
  > EOF
  
  unsat

Exact conversion of bit-vectors that fit in the format: the result is finite,
its real value is the integer, and it is positive if unsigned.

  $ alt-ergo --reproducible-resource-limit 3000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 8))
  > (assert (< 300.0 (fp.to_real ((_ to_fp_unsigned 8 24) RTZ b))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 3000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 8))
  > (assert (< (fp.to_real ((_ to_fp 8 24) RTZ b)) (- 128.0)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 8))
  > (assert (fp.isInfinite ((_ to_fp_unsigned 8 24) RTP b)))
  > (check-sat)
  > EOF
  
  unsat

Not exact in Float32, so this must not be unsat.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 32))
  > (assert (= (fp.to_real ((_ to_fp_unsigned 8 24) RNE b)) 16777216.0))
  > (assert (not (= b #x01000000)))
  > (check-sat)
  > EOF
  
  unknown

FP -> BV conversion of an exact BV -> FP conversion: the bit-vector, extended.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 16))
  > (assert (not (= b ((_ fp.to_ubv 16) RTZ ((_ to_fp_unsigned 11 53) RTZ b)))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 24))
  > (assert (not (= ((_ sign_extend 8) b)
  >   ((_ fp.to_sbv 32) RNE ((_ to_fp 11 53) RTZ b)))))
  > (check-sat)
  > EOF
  
  unsat

Also when the exact conversion is only known through an equality.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 16))
  > (declare-const x Float64)
  > (assert (not (= ((_ zero_extend 16) b) ((_ fp.to_ubv 32) RNE x))))
  > (assert (= x ((_ to_fp_unsigned 11 53) RTZ b)))
  > (check-sat)
  > EOF
  
  unsat

Not every value fits in 8 bits (unspecified result), so this must not be unsat.

  $ alt-ergo --steps-bound 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 16))
  > (assert (= ((_ fp.to_ubv 8) RTZ ((_ to_fp_unsigned 11 53) RTZ b))
  >   ((_ extract 7 0) b)))
  > (check-sat)
  > EOF
  
  unknown

A narrowing conversion that rounds toward zero overflows to the largest finite
value, not to an infinity, so these must not be unsat.

  $ alt-ergo --steps-bound 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float64)
  > (declare-const y Float32)
  > (assert (= x (fp #b0 #b11111111110 #x0000000000000)))
  > (assert (= y ((_ to_fp 8 24) RTZ x)))
  > (assert (= y (fp #b0 #b11111110 #b11111111111111111111111)))
  > (check-sat)
  > EOF
  
  unknown

  $ alt-ergo --steps-bound 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float64)
  > (assert (fp.isNegative x))
  > (assert (not (fp.isInfinite x)))
  > (assert (fp.lt x (fp #b1 #b11110000000 #x0000000000000)))
  > (assert (not (fp.isInfinite ((_ to_fp 8 24) RTP x))))
  > (check-sat)
  > EOF
  
  unknown

Sign and injectivity of fp when it is not NaN by assumption, not by its bits.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s (_ BitVec 1))
  > (declare-const e (_ BitVec 8))
  > (declare-const m (_ BitVec 23))
  > (assert (not (fp.isNaN (fp s e m))))
  > (assert (= s #b1))
  > (assert (fp.isPositive (fp s e m)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 5000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const s1 (_ BitVec 1))
  > (declare-const e1 (_ BitVec 8))
  > (declare-const m1 (_ BitVec 23))
  > (declare-const s2 (_ BitVec 1))
  > (declare-const e2 (_ BitVec 8))
  > (declare-const m2 (_ BitVec 23))
  > (assert (= (fp s1 e1 m1) (fp s2 e2 m2)))
  > (assert (not (fp.isNaN (fp s1 e1 m1))))
  > (assert (not (= s1 s2)))
  > (check-sat)
  > EOF
  
  unsat

IEEE evaluation of the operators on literals.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (= (fp.fma RNE (fp #b0 #b10000 #b0100000000) (fp #b1 #b01111 #b1000000000) (fp #b0 #b10001 #b0000000001)) (fp #b0 #b01101 #b0000010000))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (= (fp.sqrt RTP ((_ to_fp 5 11) RNE 2.0)) (fp #b0 #b01111 #b0110101001))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (= (fp.div RTZ ((_ to_fp 3 5) RNE 1.0) ((_ to_fp 3 5) RNE 3.0)) (fp #b0 #b001 #x5))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (= (fp.roundToIntegral RNA ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 3.0))))
  > (check-sat)
  > EOF
  
  unsat

is_normal and is_subnormal: exclusive classes, one of the five classes holds,
and definition by the real value.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.isNormal x))
  > (assert (fp.isSubnormal x))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (not (fp.isNaN x)))
  > (assert (not (fp.isInfinite x)))
  > (assert (not (fp.isZero x)))
  > (assert (not (fp.isNormal x)))
  > (assert (not (fp.isSubnormal x)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.isSubnormal x))
  > (assert (fp.gt x ((_ to_fp 8 24) RNE 0.5)))
  > (check-sat)
  > EOF
  
  unsat

Evaluation of the operators on known arguments, fields of fp from the
predicates, and propagation of the predicates through the operators.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (= x ((_ to_fp 8 24) RNE 1.5)))
  > (assert (= y ((_ to_fp 8 24) RNE 2.25)))
  > (assert (not (= (fp.mul RNE x y) ((_ to_fp 8 24) RNE 3.375))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const e (_ BitVec 8))
  > (declare-const m (_ BitVec 23))
  > (declare-const s (_ BitVec 1))
  > (assert (fp.isNormal (fp s e m)))
  > (assert (= e #x00))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.isNaN (fp.min x y)))
  > (assert (not (fp.isNaN x)))
  > (check-sat)
  > EOF
  
  unsat

Extensionality: finite floats with the same real value are equal, except for
zeros of different signs.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 11 53))
  > (assert (fp.isNormal x))
  > (assert (= (fp.to_real ((_ to_fp 8 24) RTZ x)) 1.5))
  > (assert (not (= ((_ to_fp 8 24) RTZ x) ((_ to_fp 8 24) RNE 1.5))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const y (_ FloatingPoint 8 24))
  > (declare-const z (_ FloatingPoint 8 24))
  > (assert (fp.isNormal y))
  > (assert (= (fp.to_real y) (fp.to_real z)))
  > (assert (not (fp.isNaN z)))
  > (assert (not (fp.isInfinite z)))
  > (assert (not (= y z)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const y (_ FloatingPoint 8 24))
  > (declare-const z (_ FloatingPoint 8 24))
  > (assert (fp.isZero y))
  > (assert (= (fp.to_real y) (fp.to_real z)))
  > (assert (not (fp.isNaN z)))
  > (assert (not (fp.isInfinite z)))
  > (assert (not (= y z)))
  > (check-sat)
  > EOF
  
  unknown

Comparisons decided from the classes and signs of their arguments, or by
evaluation.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (= x (_ -oo 8 24)))
  > (assert (not (fp.leq ((_ to_fp 11 53) RNA x) ((_ to_fp 11 53) RNE (- 26.0)))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (fp.geq (_ -zero 8 24) ((_ to_fp 8 24) RNE (- 33.25)))))
  > (check-sat)
  > EOF
  
  unsat

Conversions of bit-vectors: never NaN nor subnormal, positive if unsigned, and
inverted when exact.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 24))
  > (assert (fp.isSubnormal ((_ to_fp 5 11) RNA b)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 16))
  > (assert (fp.leq ((_ to_fp_unsigned 5 11) RTP b) ((_ to_fp 5 11) RNE (- 30377.0))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const b (_ BitVec 24))
  > (assert (= ((_ to_fp_unsigned 11 53) RTP b) ((_ to_fp 11 53) RNE 17.5)))
  > (check-sat)
  > EOF
  
  unsat

The real value of a float whose value is known: 0 for both zeros, none for
infinities.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 11 53))
  > (assert (= x (_ -zero 11 53)))
  > (assert (not (= (fp.to_real x) 0.0)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 11 53))
  > (assert (= x (_ +oo 11 53)))
  > (assert (= (fp.to_real x) 5.0))
  > (check-sat)
  > EOF
  
  unknown

fp.rem: the quotient is rounded to the nearest integer, ties to even, and a
zero result has the sign of x.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (assert (not (and
  >   (= (fp.rem ((_ to_fp 8 24) #x40a00000) ((_ to_fp 8 24) #x40000000))
  >     ((_ to_fp 8 24) #x3f800000))
  >   (= (fp.rem ((_ to_fp 8 24) #x40e00000) ((_ to_fp 8 24) #x40000000))
  >     ((_ to_fp 8 24) #xbf800000))
  >   (= (fp.rem ((_ to_fp 8 24) #xc0800000) ((_ to_fp 8 24) #x40000000))
  >     (_ -zero 8 24))
  >   (= (fp.rem ((_ to_fp 8 24) #x3fc00000) (_ +oo 8 24))
  >     ((_ to_fp 8 24) #x3fc00000))
  >   (fp.isNaN (fp.rem (_ -oo 8 24) ((_ to_fp 8 24) #x3f800000)))
  >   (fp.isNaN (fp.rem ((_ to_fp 8 24) #x3f800000) (_ -zero 8 24))))))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 4 6))
  > (declare-const y (_ FloatingPoint 4 6))
  > (assert (= x (fp #b1 #b0001 #b00010)))
  > (assert (= y (fp #b1 #b0101 #b00000)))
  > (assert (not (= (fp.rem x y) x)))
  > (check-sat)
  > EOF
  
  unsat

Special cases of fp.rem deduced from the classes of its arguments.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (or (fp.isInfinite x) (fp.isZero y)))
  > (assert (not (fp.isNaN (fp.rem x y))))
  > (check-sat)
  > EOF
  
  unsat

fp.rem facts: |rem x y| <= |y| / 2.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (not (fp.isNaN x)))
  > (assert (not (fp.isInfinite x)))
  > (assert (not (fp.isNaN y)))
  > (assert (not (fp.isInfinite y)))
  > (assert (not (fp.isZero y)))
  > (assert (fp.gt (fp.abs (fp.rem x y)) (fp.abs y)))
  > (check-sat)
  > EOF
  
  unsat

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (not (fp.isNaN x)))
  > (assert (not (fp.isInfinite x)))
  > (assert (fp.eq y ((_ to_fp 8 24) RNE 4.0)))
  > (assert (fp.gt (fp.rem x y) ((_ to_fp 8 24) RNE 2.5)))
  > (check-sat)
  > EOF
  
  unsat

Satisfiable, so this must not be unsat.

  $ alt-ergo --steps-bound 1000 -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.eq (fp.rem x y) ((_ to_fp 8 24) RNE 1.0)))
  > (check-sat)
  > EOF
  
  unknown

With a literal [y], the remainder is [x - y * n] for the integer [n] nearest to
[x / y].

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (fp.lt ((_ to_fp 8 24) RNE 2.0) x))
  > (assert (fp.lt x ((_ to_fp 8 24) RNE 2.5)))
  > (assert (not (fp.lt (fp.rem x ((_ to_fp 8 24) RNE 2.0))
  >                     ((_ to_fp 8 24) RNE 0.5))))
  > (check-sat)
  > EOF
  
  unsat

Floats are discrete: nothing lies strictly between two consecutive floats.
Reasoning only through [to_real] leaves an open real interval, so these were
answered [unknown]; [Fpa_rel] now tightens a strict bound to the adjacent float.

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x Float32)
  > (assert (fp.lt (fp #b0 #b01111111 #b00000000000000000000000) x))
  > (assert (fp.lt x (fp #b0 #b01111111 #b00000000000000000000001)))
  > (check-sat)
  > EOF
  
  unsat


The same through [fp.leq] with the endpoint excluded.

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x Float32)
  > (assert (not (fp.leq x (fp #b0 #b01111111 #b00000000000000000000000))))
  > (assert (fp.leq x (fp #b0 #b01111111 #b00000000000000000000001)))
  > (assert (not (fp.eq x (fp #b0 #b01111111 #b00000000000000000000001))))
  > (check-sat)
  > EOF
  
  unsat


With a float in between (two ulps above 1.0) the bound must not collapse.

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x Float32)
  > (assert (fp.lt (fp #b0 #b01111111 #b00000000000000000000000) x))
  > (assert (fp.lt x (fp #b0 #b01111111 #b00000000000000000000010)))
  > (check-sat)
  > EOF
  
  unknown


Exact operations: the products by powers of two in range.

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x Float32)
  > (assert (fp.isNormal x))
  > (assert (fp.lt (fp.abs x) ((_ to_fp 8 24) RNE 1000.0)))
  > (assert (not (fp.eq (fp.div RNE (fp.mul RNE x ((_ to_fp 8 24) RNE 4.0))
  >                             ((_ to_fp 8 24) RNE 4.0)) x)))
  > (check-sat)
  > EOF
  
  unsat


The remainder: a zero has the sign of [x].

  $ alt-ergo -o smtlib2 2>/dev/null <<EOF
  > (set-logic QF_FP)
  > (declare-const x Float32)
  > (declare-const y Float32)
  > (assert (fp.isNegative x))
  > (assert (fp.isNormal x))
  > (assert (fp.isNormal y))
  > (assert (fp.isZero (fp.rem x y)))
  > (assert (fp.isPositive (fp.rem x y)))
  > (check-sat)
  > EOF
  
  unsat

Models only contain the user's symbols

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (< (fp.to_real ((_ to_fp 8 24) RNE 1.5)) r))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun r () Real (/ 5 2))
  )

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const r Real)
  > (assert (= r 0.1))
  > (assert (fp.isNormal ((_ to_fp 8 24) RNE r)))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun r () Real (/ 1 10))
  )

Model generation gives each float a literal

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (assert (< 1.0 (fp.to_real x)))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 8 24)
     (fp #b0 #b10000000 #b00000000000000000000000))
  )

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 11 53))
  > (assert (= (fp.to_real x) 0.75))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 11 53)
     (fp #b0 #b01111111110 #b1000000000000000000000000000000000000000000000000000))
  )

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (declare-const m RoundingMode)
  > (assert (= y (fp.add m x x)))
  > (assert (fp.isInfinite x))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 8 24) (_ -oo 8 24))
    (define-fun y () (_ FloatingPoint 8 24) (_ -oo 8 24))
    (define-fun m () RoundingMode RTN)
  )

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (fp.isNaN x))
  > (assert (fp.isNegative y))
  > (assert (fp.isZero y))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 8 24) (_ NaN 8 24))
    (define-fun y () (_ FloatingPoint 8 24) (_ -zero 8 24))
  )

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (declare-const z (_ FloatingPoint 8 24))
  > (assert (not (or (fp.isZero x) (fp.isNaN x) (fp.isInfinite x))))
  > (assert (not (or (fp.isZero y) (fp.isNaN y) (fp.isInfinite y))))
  > (assert (not (or (fp.isZero z) (fp.isNaN z) (fp.isInfinite z))))
  > (assert (distinct x y z))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 8 24)
     (fp #b1 #b01111111 #b00000000000000000000000))
    (define-fun y () (_ FloatingPoint 8 24)
     (fp #b1 #b10000000 #b00000000000000000000000))
    (define-fun z () (_ FloatingPoint 8 24)
     (fp #b1 #b10000000 #b10000000000000000000000))
  )

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 8 24))
  > (declare-const y (_ FloatingPoint 8 24))
  > (assert (not (fp.isNaN x)))
  > (assert (not (fp.eq x y)))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 8 24) (_ -oo 8 24))
    (define-fun y () (_ FloatingPoint 8 24) (_ NaN 8 24))
  )

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 5 11))
  > (declare-const y (_ FloatingPoint 5 11))
  > (assert (fp.lt x y))
  > (assert (fp.lt (fp #b0 #b01111 #b0000000000) x))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 5 11) (fp #b0 #b01111 #b0000000001))
    (define-fun y () (_ FloatingPoint 5 11) (_ +oo 5 11))
  )

When every literal is known to be distinct from a float, model generation
proposes one anyway so that the search backtracks, instead of leaving the
float without a value. This query used to crash, now it times out.

  $ alt-ergo --reproducible-resource-limit 2000 -o smtlib2 --produce-models 2>/dev/null <<EOF
  > (set-logic ALL)
  > (declare-const x (_ FloatingPoint 3 5))
  > (declare-const y (_ FloatingPoint 3 5))
  > (declare-const z (_ FloatingPoint 3 5))
  > (assert (fp.leq (fp #b0 #b010 #b1111) x))
  > (assert (not (fp.isNaN x)))
  > (assert (fp.leq (fp #b0 #b101 #b0011) y))
  > (assert (not (fp.isNaN y)))
  > (assert (fp.leq z (fp #b1 #b110 #b0000)))
  > (assert (not (fp.isNaN z)))
  > (assert (not (fp.isInfinite (fp.roundToIntegral RNA x))))
  > (check-sat)
  > (get-model)
  > EOF
  
  unknown
  (
    (define-fun x () (_ FloatingPoint 3 5) (fp #b0 #b010 #b1111))
    (define-fun y () (_ FloatingPoint 3 5) (_ +oo 3 5))
    (define-fun z () (_ FloatingPoint 3 5) (_ -oo 3 5))
  )

