
# Theories

Alt-Ergo has built-in support for many different theories.

Those theories allow to reason about values of various types. To learn more about the syntax and semantic of those types, as well as operators defined on them, please refer to section [Types](02_types/index).

## Native theories

Alt-Ergo works using a polymorphic first-order logic.
A precise definition of what is meant here by 'theory' can be found in the second chapter of [this thesis](https://tel.archives-ouvertes.fr/file/index/docid/842555/filename/VD2_IGUERNELALA_MOHAMED_10062013.pdf).

Alt-Ergo currently provides built-in support for the following theories.

* The free theory of equality with uninterpreted symbols
* Associative and commutative (AC) symbols
* Linear arithmetic over integers and rationals
* (Fragment of) non-linear arithmetic
* Floating-point arithmetic (as an extension)
* Enumerated datatypes
* Record datatypes
* Polymorphic functional arrays
* Fixed-size bitvectors

Theories that can be built upon in user-defined extensions are named in the following way.
All theories are always considered *modulo equality*.

* `SUM`: Enumerated datatypes
* `Adt`: Algebraic datatypes
* `Arrays`: Polymorphic functional arrays
* `Records`: Record datatypes
* `Bitv`: Fixed-size bitvectors
* `LIA`: Linear arithmetic over integers
* `LRA`: Linear arithmetic over rationals
* `NIA`: Non-linear arithmetic over integers
* `NRA`: Non-linear arithmetic over rationals
* `FPA`: Floating-point arithmetic


## Floating-point Arithmetic

Alt-Ergo implements partial support for floating-point arithmetic. More
precisely, Alt-Ergo implements the second and third layers from the paper "[A
Three-tier Strategy for Reasoning about Floating-Point Numbers in
SMT](https://inria.hal.science/hal-01522770)" by Conchon et al.

*Note*: Support for floating-point arithmetic is enabled by default in Alt-Ergo since version 2.6.0.

Versions 2.5.x required to use the command line flag `--enable-theory fpa` and previous versions used the external prelude mechanism and required command line flags `--use-fpa` and `--prelude fpa-theory-2019-10-08-19h00.ae`.

This means that Alt-Ergo doesn't actually support a floating-point type (that
may come in a future release); instead, it supports a rounding function, as
described in the paper.  The rounding function transforms a real into the
nearest representable float, according to the standard floating-point rounding
modes. Unlike actual floats, there are no NaNs or infinites, and there is no
overflow (but there is underflow): one way to think about the underlying data
type is as floats with a potentially infinite exponent.

NaNs, infinites, and overflows must be handled outside of Alt-Ergo by an
implementation of the three-tier strategy described in the paper (this is done
automatically in Why3 when you use floats).

The rounding function is available as a builtin function called `float`:

```alt-ergo
type fpa_rounding_mode =
  | NearestTiesToEven
    (** To nearest, tie breaking to even mantissa *)
  | ToZero
    (** Round toward zero *)
  | Up
    (** Round toward plus infinity *)
  | Down
    (** Round toward minus infinity *)
  | NearestTiesToAway
    (** To nearest, tie breaking away from zero *)

(** The first int [prec] is the mantissa's size, including the implicit bit.

    The second int [exp] is the absolute value of the exponent of the smallest
    representable positive number. Note that this is not the `emin` value
    defined in IEEE-754, which represents the minimum exponent of the smallest
    normal positive number.

    The result of a call to [float(prec, exp, rm, x)] is always of the form:

      (-1)^s * c * 2^q

    where [s] is [0] or [1], [c] is an integer with at most [prec - 1] binary
    digits (that is, [0 <= c < 2^(prec - 1)]), and [q >= exp] is an integer.

    Given `eb` the number of bits of the exponent and `sb` the number of bits
    of the significand (including the hidden bit), `prec` and `exp` are
    computed as follows:

      prec = sb
      exp = (1 lsl (eb - 1)) + sb - 3 *)
logic float: int, int, fpa_rounding_mode, real -> real
```

The `float` function *must* be called with concrete values for its first 3
arguments, using other symbolic expressions is not supported and will result in
an error (defining functions that call `float` is also possible, as long as the
corresponding arguments of the wrapping function are only called with concrete
values).

Alt-Ergo also exposes convenience functions specialized for standard
floating-point types:

```alt-ergo
function float32(m: fpa_rounding_mode, x: real): real = float(24, 149, m, x)
function float32d(x: real): real = float32(NearestTiesToEven, x)
function float64(m: fpa_rounding_mode, x: real): real = float(53, 1074, m, x)
function float64d(x: real): real = float64(NearestTiesToEven, x)
```

These functions are currently only available when using the native language;
they are not available when using the smtlib2 input format.

Finally, the `integer_round` function allows rounding a real to an integer
using the aforementioned rounding modes:

```alt-ergo
logic integer_round : fpa_rounding_mode, real -> int
```

Here is an example:

```alt-ergo
goal g: integer_round(ToZero, 2.1) = 2
```

## User-defined extensions of theories

[TODO: document]

### `theory [...] extends [...] = [...] end`

### `case_split`

### Semantic triggers

In addition to syntactic triggers (or triggers) and interval triggers (or filters) defined in [axioms](03_declaration_of_axioms.md), additional triggers are available inside theories.
Those additional triggers are called semantic triggers.

They correspond to the following constructs.

#### Syntax

```
<semantic_trigger>    ::= <in_interval_trigger> | <maps_to_trigger>
(* [COMMENT/TODO: seems to always be paired with 'interval triggers'/filters *)
<in_interval_trigger> ::= <id> 'in' <square_bracket> <bound> ',' <bound> <square_bracket>
(* [COMMENT/TODO: probably there to shorten axioms] *)
<maps_to_trigger>     ::= <alias_id> '|->' <expr>
```

[TODO: complete this explanation]
