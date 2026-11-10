
# Declaration of symbols 

In order to introduce the problem's vocabulary, the user can declare its own symbols.
* Simple variables and uninterpreted functions.
* Associative and commutative symbols (a special case of uninterpreted functions).
* Interpreted functions.
* Predicated (a special case of interpreted functions).

## `logic`: uninterpreted symbols

The `logic` keyword allows the user to define new uninterpreted (typed) symbols.
Those symbols may be used to represent simple variables, uninterpreted functions, data structures, ...
Constraints on those symbols may be added via the `axiom` keyword.

Please refer to section [Types](02_types/index) for more information on the types of symbols that can be created.

### Syntax
```
<logic_declaration> ::= "logic" <identifier_list> ":" <type>
<identifier_list>   ::= <identifier> ( "," <identifier> )*
```

### Examples
```
(* Introducing propositional variables *)
logic p,q,r: prop

axiom a: p and q -> r
goal g: p -> r
```

```
(* Introducing uninterpreted functions *)
logic f: int -> int
axiom a1: forall x:int. f(x)>0
goal g1: f(1)>=0
```

```
(* Functions can have multiple arguments *)
logic h, g, f: int, int -> int
logic a, b: int

goal g_2 :
    h(g(a,a),g(b,b)) = g(b,b) ->
    a = b ->
    g(f(h(g(a,a),g(b,b)),b) - f(g(b,b),a),
      f(h(g(a,a),g(b,b)),a) - f(g(b,b),b)) = g(0,0)
```

```
(* Axioms can be used to add constraints *)
logic Ack: int, int -> int
axiom Ack_n:
    forall n:int.
        Ack(0,n)=n+1
axiom Ack_m:  
    forall m:int. m>0 ->
        Ack(m,0) = Ack(m-1,1)
axiom Ack_nm: 
    forall n,m:int. n>0 -> m>0 ->
        Ack(m,n) = Ack(m-1,Ack(m,n-1)) 
```

## `ac` modifier: associative and commutative symbols

When creating a new uninterpreted symbol trough the `logic` keyword, the user can add the `ac` modifier to inform Alt-Ergo that this symbol is associative and commutative (AC).
Using this symbol makes it possible to take advantage of Alt-Ergo's built-in support for AC-symbols.

Most automated theorem provers have difficulties in handling associative and commutative symbols.
It is indeed possible to write
```
logic f: int, int -> int
axiom associative: forall x,y,z:int. f(f(x,y),z) = f(x,f(y,z))
axiom commutative: forall x,y:int. f(x,y) = f(y,x)
```
However, handling universally-quantified axioms is challenging for this kind of solvers. It is necessary to create 'instances' of those axioms in order to use them, and the number of instances can quickly become overwhelming.

In Alt-Ergo's native language, one can simply write
```
logic ac f: int, int -> int
```
in order to specify that `f` is an AC-symbol. Once this is done, Alt-Ergo will use the built-in [AC(X) algorithm](https://www.lri.fr/~conchon/publis/conchon-lmcs2012.pdf) to handle this symbol much more efficiently than what would have been possible through axioms.

### Syntax
```
<logic_ac_declaration> ::= "logic" "ac" <identifier_list> ":" <type>
<identifier_list>      ::= <identifier> ( "," <identifier> )*
```

### Examples
```
type person
(* Last common ancestor *)
logic ac lca: person, person -> person
logic Alice, Bob, Eve: person

goal g: lca(Alice, lca(Bob, Eve)) = lca(Eve, lca(Alice, Bob))
```

```
logic ac u: int, int -> int
goal g1: u(1,u(2,u(3,u(4,5)))) = u(u(u(u(5,4),3),2),1)
goal g2: forall a,b,c,v,w:int. u(a,b) = w and u(a,c) = v -> u(b,v) = u(c,w)
```

## `function`: user-defined functions

Using the `function` keyword, the user can add its own (interpreted) functions.

### Syntax
```
<function_declaration>    ::= "function" <function_id> "(" <function_parameter_list> ")" ":" <output_type> "=" <function_body>
<function_parameter_list> ::= <function_parameter> ( "," <function_parameter> )*
<function_parameter>      ::= <parameter_id> ":" <parameter_type>
<function_body>           ::= <expression>
```

### Examples
```
function abs(x:int):int =
    if x>=0 then (x) else (-x)

goal g: forall x:int. abs(x)>=0
```

```
type person
logic father_of: person, person -> prop
logic mother_of: person, person -> prop

function son_of(kid:person, parent:person):bool =
    father_of(parent, kid) or mother_of(parent, kid)
```

## `predicate`: propositional valued functions

The `predicate` construct allows to user to define (interpreted) functions whose codomain is of type `prop`.

It is possible to create "ground predicates", i.e. predicates with no arguments.

Since Alt-Ergo 2.3.0, `prop` and `bool` have the same behaviour: `predicate` can therefore be seen as a shorthand for as boolean-valued `function`.
See section [Types](02_types/index) for more information on the `prop`/`bool` keywords.

### Syntax
```
<predicate_declaration>    ::= "predicate" <predicate_id> ( "(" <predicate_parameter_list> ")" )? "=" <predicate_body>
<predicate_parameter_list> ::= <predicate_parameter> ( "," <predicate_parameter> )*
<predicate_parameter>      ::= <predicate_id> ":" <predicate_type>
<predicate_body>           ::= <expression>
```

### Examples
```
type person
logic father_of: person, person -> prop
logic mother_of: person, person -> prop

predicate son_of(kid:person, parent:person) =
    father_of(parent, kid) or mother_of(parent, kid)
```
