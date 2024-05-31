
# SMT-LIB Version 2

Alt-Ergo has partial support for the [SMT-LIB
standard](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf)
language from the SMT community.

*Note*: As of version 2.5.0, enhanced support for the SMT-LIB language is
provided by the new [Dolmen](http://gbury.github.io/dolmen/) frontend.

## Bit-vectors

Since version 2.5.0, Alt-Ergo has partial support for the `FixedSizeBitVectors`
theory and the `QF_BV` and `BV` logics. All the symbols from these logics are
available, although reasoning using them is limited and incomplete for now.

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

*Note*: While Alt-Ergo has built-in support for **computing** with `ae.round`
on known arguments, reasoning capabilities involving `ae.round` on non-constant
arguments are disabled by default and currently requires to use the flag
`--enable-theories fpa`.

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
binary digits (i.e. `0 <= c < 2^(prec - 1)`) and `q >= exp` is an integer.

The following function symbols are provided as short synonyms for common
floating point representations:

 - `ae.float16` is a synonym for `(_ ae.round 11 24)`
 - `ae.float32` is a synonym for `(_ ae.round 24 149)`
 - `ae.float64` is a synonym for `(_ ae.round 53 1074)`
 - `ae.float128` is a synonym for `(_ ae.round 113 16494)`
