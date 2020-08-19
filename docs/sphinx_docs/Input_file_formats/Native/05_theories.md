 
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


### About floating-point arithmetic

Floating-point arithmetic (FPA) is a recent addition to Alt-Ergo, and is not documented here.
To use it, it is necessary to load the corresponding prelude. The strategy used to handle FPA is based on over-approximation by intervals of reals, and roundings.
More information on this strategy and the language extension can be found in [this article](https://hal.inria.fr/hal-01522770).


## User-defined extensions of theories

[TODO: document]

### `theory [...] extends [...] = [...] end`

### `case_split`

### Semantic triggers

In addition to syntactic triggers (or triggers) and interval triggers (or filters) defined in [section Axioms](03_declaration_of_axioms.md), additional triggers are available inside theories.
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
