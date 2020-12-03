# Summary

1. [Declaration of symbols](01_declaration_of_symbols.md).
    Declaration of the problem's vocabulary: simple variables, uninterpreted and interpreted functions, as well as predicates.
2. [Native types and declaration of types](02_types/index)
    Alt-Ergo comes with various built-in types, which correspond to theories handled by built-in solvers.
    The user can also declare new types thanks to Alt-Ergo's rich and polymorphic type system à la ML.
3. [Declaration of axioms](03_declaration_of_axioms.md)
    Specification of the problem's structure: stating facts by declaring axioms
4. [Setting goals](04_setting_goals.md)
    Defining what must be proven.
5. [Theories](05_theories.md)
    Alt-Ergo implements (semi-)decision procedures for various theories.
    It is possible to add new theories.
6. [Control Flow](06_control_flow.md)
    Specific constructs: `if [...] then [...] else [...]`, `let [...] in [...]` or `match [...] with [...]`
7. [Syntax of declarations and expressions](07_syntax_of_declarations_and_expressions.md)
    Additional information on Alt-Ergo's syntax, defined in [BNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form).
    In particular, legal expressions are defined here.

## Keywords

Reserved keywords are the following.
* To add new uninterpreted symbols (variables or functions) to the signature: [`logic`](01_declaration_of_symbols.html#logic-uninterpreted-symbols) and the [`ac` modifier](01_declaration_of_symbols.html#ac-modifier-associative-and-commutative-symbols) for associative and commutative symbols.
* Interpreted functions: [`function`](01_declaration_of_symbols.html#function-user-defined-functions) and [`predicate`](01_declaration_of_symbols.html#predicate-propositional-valued-functions).
* Built-in types: [`int`](02_types/02_01_builtin.html#numbers-int-real-and-floats), [`real`](02_types/02_01_builtin.html#numbers-int-real-and-floats), [`bool`](02_types/02_01_builtin.html#bool-and-prop), [`prop`](02_types/02_01_builtin.html#bool-and-prop), [`unit`](02_types/02_01_builtin.html#unit), [`bitv`](02_types/02_01_builtin.html#bitvectors-bitv), [`farray`](02_types/02_01_builtin.html#functional-polymorphic-arrays-farray).
* Constant and operators for propositions are available: `and`, `or`, `xor`, `not`, `true`, `false`. The construct `distinct` is available for all types. Quantifiers `forall` and `exists` can be used.
* To create new types: [`type`](02_types/index). They keyword `of` is useful when dealing with structured datatypes, which include [records](02_types/02_02_user_defined.html#records), [enums](02_types/02_02_user_defined.html#enums-and-algebraic-datatypes) and [algebraic datatypes](02_types/02_02_user_defined.html#enums-and-algebraic-datatypes).
* To declare new axioms: [`axiom`](03_declaration_of_axioms.html#axiom), and the special case [`rewriting`](03_declaration_of_axioms.html#rewriting). 
* To define goals that must be proven valid: [`goal`](04_setting_goals.html#goal). [`cut`](04_setting_goals.html#intermediate-goals-cut-and-check) and [`check`](04_setting_goals.html#intermediate-goals-cut-and-check) can create intermediate goals that won't interact with other goals through [triggers](03_declaration_of_axioms.html#triggers).
* New theories may be defined using [theory](05_theories.html#theory-extends-end) (and the keywords `extends` and `end`). Inside theories, [`axiom`](05_theories.html#axiom) can be used with [additional triggers](05_theories.html#semantic-triggers). The construct [`case_split`](05_theories.html#case-split) is also available.
* Other useful constructs are [`let` [...] `in`](06_control_flow.html#let-in), [`match` [...] `with` [...] `end`](06_control_flow.html#match-with) and [`if` [...] `then` [...] `else` [...]](06_control_flow.html#if-then-else).

The list of all reserved keywords, in alphabetical order, is:
```
ac, and, axiom, bitv, bool, case_split, check, cut, distinct, else, end, exists, extends,
false, forall, function, goal, if, in, int, let, logic, not, xor, predicate, prop, 
real, rewriting, then, theory, true, type, unit, void, match, with, of
```
Note that preludes (additional theories which may be loaded) may reserve more keywords.
