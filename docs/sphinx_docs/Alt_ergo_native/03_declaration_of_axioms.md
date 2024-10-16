
# Declaration of axioms

Axioms may be used to state facts which can be used by the solver.

Alt-Ergo handles universal formula through an instantiation mechanism. In other words, any formula containing `forall x:t.` must be instantiated for a specific `x` before it can be used.
The heuristic for choosing new instances is based on *triggers*. By default, triggers are automatically chosen by Alt-Ergo, but it is also possible for the user to specify its own triggers (for improved efficiency in using those axioms).

## `axiom`

In order to declare an axiom, the user can use the following construct.
Note that axioms must always be named.

### Syntax
```
<axiom_declaration> ::= 'axiom' <id> ':' <axiom_body>
```
Here, `<axiom_body>` is an expression which may contain quantifiers, and where user-specified triggers may be added to universal quantifiers.

### Example

```
(* Axioms can be used without quantifiers *)
logic x:bitv[4]
logic y,z:int

axiom a1: x^{0,1}=[|11|]
axiom a2: y=3 and z<4
```

```
(* Simple example with an universal quantifier *)
logic f:int->int
axiom f_pos: forall x:int. f(x)>=0
```

## Triggers
The heuristic used by Alt-Ergo to partially handle quantified formula relies on triggers.

A  trigger  is  a  list  of patterns that restrict instantiation to known (ground) terms that have a given form. For instance, if `P(x)` is used as an instantiation pattern for the following axiom `ax1`
```
logic P,Q,R : int -> prop
axiom ax1 : forall x:int. (P(x) or Q(x)) -> R(x)
goal g1 : P(1) -> R(1)
goal g2 : Q(2) -> R(2)
```
then,  among  the  set `{P(1), R(1), Q(2), R(2)}` of  known  terms, only `P(1)` can be used by the matching algorithm to create the instance `((P(1) or Q(1)) -> R(1)` of `ax1` , which implies that only `g1` is proved.

A good choice of triggers is crucial. With too few triggers, or with irrelevant triggers, true things won't be proven. With too many triggers, too many instances will be created, and Alt-Ergo will spend its time in irrelevant branches of the search space.

Triggers are automatically generated by Alt-Ergo, but Alt-Ergo's native language also allows the user to specify its own triggers.

Triggers are separated in 'syntactic triggers' (or simply 'triggers') and 'interval triggers' (or 'filters').
Syntactic triggers are matched *modulo equality*: an instance of the axiom will be created whenever a known term matches this pattern *modulo equality*. 
Interval triggers further restrict instantiation of axioms, and check that variables are within intervals.

Multiple patterns can be used in syntactic triggers. They are separated by `|` which means 'or' and by `,` which means 'and'. `|` has an higher precedence than `,`.

### Syntax
```
<quantified_formula>    ::= <quantifier> <var_id_list_sep_comma> ':' <var_type> <syntactic_triggers>? <interval_triggers>? '.' <expr>
<quantifier>            ::= 'exists' | 'forall'
<var_id_list_sep_comma> ::= <id> ( ',' <id> )*
<syntactic_triggers>    ::= '[' <trigger> ( '|' <trigger> )* ']'
<trigger>               ::= <pattern> ( ',' <pattern> )*
```

Interval triggers also exists. [TODO: add more explanations]

```
<interval_triggers>     ::= '[' <filter> ( ',' <filter> )* ']'
(* According to p.12 of https://hal.inria.fr/hal-01522770/document. This doesn't seem to work *)
<filter>                ::= <bound> <rel> <term> | <term> <rel> <bound>
<bound>                 ::= <numerical_constant> | <quantified variable>
<rel>                   ::= '<' | '<='
```

[Semantic triggers](05_theories.md#semantic-triggers) are only available in theories

### Examples
```
(* P(x) used as the only trigger *)
logic P,Q,R: int -> prop
axiom ax1: forall x:int [P(x)]. (P(x) or Q(x)) -> R(x)
goal g1: P(1) -> R(1)
goal g2: Q(2) -> R(2)
```

```
(* Several triggers available *)
logic P, Q, R: int -> prop
logic f: int -> int
axiom ax2: forall x,y:int [f(x), Q(y)]. P(f(x)) and Q(y) -> R(x)
```

In the following example, no ground term match `P(f(x))`, but the instance `P(f(2))` of axiom `ax` is generated by combining the ground equality `a=f(2)` and the ground term `P(a)`.

```
(* Matching occurs modulo equality *)
logic P, R: int -> prop
logic f: int -> int
axiom ax: forall x:int [P(f(x))]. P(f(x)) -> R(x)
goal g1: forall a:int. P(a) -> a = f(2) -> R(2)
```

## `rewriting`
The decision procedures at the heart of Alt-Ergo are mainly based on rewriting techniques.

To add a new axiom directly in the form of a rewriting technique, the keyword `rewriting` can be used.

[TODO: complete]

### Syntax
```
<rewriting_declaraction> ::= 'rewriting' <id> ':' <predicate_list_sep_pv>
<predicate_list_sep_pv>  ::= <predicate> (';' <predicate_list_sep_pv>? )? 
(* pre-written objects of type predicate can be used, as well as expressions that can be interpreted as predicates *) 
<predicate>              ::= <predicate_expr> | <predicate_id>
```

### Example
[TODO: find relevant examples]
