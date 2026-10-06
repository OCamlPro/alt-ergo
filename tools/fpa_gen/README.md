# fpa-gen

Generates `src/preludes/smt-lib-fpa.psmt2` from Why3's axiomatization of the
SMT-LIB FPA theory.

Why3 generates an axiomatisation for a concrete FP format (either `Float64` or
`Float32`). `fpa-gen` takes its output and generalizes it by renaming symbols
to the `ae.fp.*` namespace, adding `eb`/`sb` (exponent/significand bits)
parameters to every FP operation and quantifying axioms over them, guarding
every axiom with `(< 1 eb) && (< 1 sb)`. `fpa-gen` also automatically selects
triggers for every axiom for which Why3 did not already emit a trigger.

The prelude can be generated with:
```
make gen-fpa-prelude
```

This runs `why3 prove -P alt-ergo` on `tools/fpa_gen/files/test.mlw` to get
Why3's `Float64` axiomatization, calls `fpa-gen` on it, and writes its output to
`src/preludes/smt-lib-fpa.psmt2`.

It expects `why3` and `alt-ergo` to be installed.

`fpa-gen` can be through the command line (from alt-ergo's repo root) with:
```
dune exec -- tools/fpa_gen/main.exe [OPTION]... FILE
```
It is kind of hand-crafted to work specifically for the generated axiomatization
by Why3, it was tested with version `1.8.2`.

Command line options, all take a boolean, all true by default:
- `--pow2-builtin`: Use Alt-Ergo's builtin `int.pow2` symbol instead of the
  axiomatized `pow2`.
- `--sqrt-builtin`: Use Alt-Ergo's builtin `sqrt_real` symbol instead of the
  axiomatized `sqrt2`.
- `--inline-functions`: Inline calls to defined functions (currently there are
  no recursive functions).
- `--select-triggers`: Automatically select triggers for axioms that don't have
  any.
