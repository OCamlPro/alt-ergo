# SMT-LIB language

Since version 2.5.0, Alt-Ergo supports the
[SMT-LIB](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf)
language from the SMT community. This support is enabled by the
[Dolmen](http://gbury.github.io/dolmen/) library.

```{note}
In version 2.5.x, the `--frontend dolmen` option is required to get full
SMT-LIB support. Starting from version 2.6.0, this option became the default
and is no longer necessary.
```

Alt-Ergo supports the following SMT-LIB [theories](https://smt-lib.org/theories.shtml):

 - The [Core](https://smt-lib.org/theories-Core.shtml) theory of booleans.
 - The [ArraysEx](https://smt-lib.org/theories-ArraysEx.shtml) theory of
   functional arrays with extensionality.
 - The
   [FixedSizeBitVectors](https://smt-lib.org/theories-FixedSizeBitVectors.shtml)
   theory of bit-vectors (since version 2.5.0).
 - The [Ints](https://smt-lib.org/theories-Ints.shtml) theory of integers[^1].
 - The [Reals](https://smt-lib.org/theories-Reals.shtml) theory of real numbers.
 - The [Reals_Ints](https://smt-lib.org/theories-Reals_Ints.shtml) theory of
   real and integer numbers[^2].

[^1]: The `abs` primitive is incomplete without the flag `--enable-theories ria`.
[^2]: The `to_real`, `to_int`, `is_int` and `abs` primitives are incomplete without
    the flag `--enable-theories ria`.

## Bit-vectors

Alt-Ergo supports the `FixedSizeBitVectors` theory, as well as the additional
symbols from the `QF_BV` and `BV` logics.

The non-standard symbols `bv2nat` and `(_ int2bv n)` (where `n >
0` is a natural number representing the target bit-vector size) for conversion
between integers and bit-vectors are supported.

## Floating-Point Arithmetic

Alt-Ergo does not currently support the `FloatingPoint` SMT-LIB theory.
Instead, Alt-Ergo implements the second and third layers described in the paper
"[A Three-tier Strategy for Reasoning about Floating-Point Numbers in
SMT](https://inria.hal.science/hal-01522770)" by Conchon et al.

Alt-Ergo provides the rounding function described in the paper by making
available all functions symbols with declarations of the form below, where
`prec` and `exp` are numerals greater than 1 and `RoundingMode` is defined in
the FloatingPoint SMT-LIB theory.

```smt-lib
((_ ae.round prec exp) RoundingMode Real Real)
```

`prec` defines the number of bits in the significand, including the hidden bit,
and is equivalent to the `sb` parameter of the `(_ FloatingPoint eb sb)` sort
in the FloatingPoint SMT-LIB theory.

`exp` defines the absolute value of the exponent of the smallest representable
positive number (this is not the same as the `emin` value defined in IEEE-754,
which is the minimum exponent of the smallest *normal* positive number). An
appropriate value for `exp` can be computed from the `eb` and `sb` parameters
of the `(_ FloatingPoint eb sb)` sort as `exp = 2^(eb - 1) + sb - 3`.

The result of `(_ ae.round prec exp)` is always of the form `(-1)^s * c * 2^q`
where `s` is a sign (`0` or `1`), `c` is an integer with at most `prec - 1`
binary digits (i.e. `0 <= c < 2^(prec - 1)`) and `q >= -exp` is an integer.

The following function symbols are provided as short synonyms for common
floating point representations:

 - `ae.float16` is a synonym for `(_ ae.round 11 24)`
 - `ae.float32` is a synonym for `(_ ae.round 24 149)`
 - `ae.float64` is a synonym for `(_ ae.round 53 1074)`
 - `ae.float128` is a synonym for `(_ ae.round 113 16494)`

### Examples

Input:

```smt-lib
(set-option :produce-models true)
(set-logic ALL)
(declare-const |0.3f32| Real)
(assert (= (ae.float32 RNE 0.3) |0.3f32|))
(declare-const |0.3f16| Real)
(assert (= (ae.float16 RNE 0.3) |0.3f16|))
(check-sat)
(get-model)
```

Output:

```smt-lib
unknown
(
  (define-fun |0.3f32| () Real (/ 5033165 16777216))
  (define-fun |0.3f16| () Real (/ 1229 4096))
)
```
