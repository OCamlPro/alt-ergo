
# SMT-LIB Version 2

Alt-Ergo has partial support for the [SMT-LIB
standard](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf)
language from the SMT community.

*Note*: As of version 2.5.0, enhanced support for the SMT-LIB language is
provided by the new [Dolmen](http://gbury.github.io/dolmen/) frontend. To use
it, pass the option `--frontend dolmen` to Alt-Ergo. This will become the
default in a future release.

## Bit-vectors

Since version 2.5.0, Alt-Ergo has partial support for the `FixedSizeBitVectors`
theory and the `QF_BV` and `BV` logics when used with the Dolmen frontend. All
the symbols from these logics are available, although reasoning using them is
limited and incomplete for now.

The non-standard symbols `bv2nat` and `(_ int2bv n)` (where `n >
0` is a natural number representing the target bit-vector size) for conversion
between integers and bit-vectors are supported.
