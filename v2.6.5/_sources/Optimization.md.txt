# Optimization

Since version 2.6.0, Alt-Ergo supports optimization for LIA and Bitvector
theories.

## MaxSMT syntax

- Use `(maximize ...)` and `(minimize ...)` statements to specify an objective function.

- Use `(get-objectives)` after `(check-sat)` to output the best values
  for each objective function.

## Activation

You only need to [enable model generation](Model_generation.md#activation).
The identifiers `maximize`, `minimize` and `get-objectives` are reserved by
default. If you want to disable the `MaxSMT` extension, use the
[strict mode](Usage/index.md#strict-mode).

```{admonition} Note
The optimization feature is only compatible with the SAT solver `CDCL-Tableaux`,
which is the default.
```

## Examples

First, consider a classical linear programming problem:
```smt-lib
(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (+ (* 5 x) (* 2 y) (* (- 0 3) z)) 25))
(assert (= (+ (* (- 0 2) x) (* 4 y)) 8))
(assert (<= x y))
(maximize x)
(check-sat)
(get-model)
(get-objectives)
```
Alt-Ergo outputs:
```smt-lib
unknown
(
  (define-fun x () Int 4)
  (define-fun y () Int 4)
  (define-fun z () Int 1)
)
(objectives
  (x 4)
)
```

- The optimization also works with an expression in `maximize`:
```smt-lib
(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (<= x 5))
(assert (<= 0 y))
(maximize (- (* 5 x) y))
(check-sat)
(get-objectives)
```
Alt-Ergo outputs:
```smt-lib
unknown
(
  (define-fun x () Int 5)
  (define-fun y () Int 0)
)
(objectives
  ((- (* 5 x) y) 25)
)
```

- Finally, an example with bitvectors:
```smt-lib
(set-option :produce-models true)
(set-logic ALL)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (bvult x (_ bv2 32)))
(assert (bvule y (_ bv10 32)))
(maximize x)
(maximize y)
(check-sat)
(get-model)
(get-objectives)
```
Alt-Ergo outputs:
```smt-lib
unknown
(
  (define-fun x () (_ BitVec 32) #x00000001)
  (define-fun y () (_ BitVec 32) #x0000000a)
)
(objectives
  (x #x00000001)
  (y #x0000000a)
)
```
