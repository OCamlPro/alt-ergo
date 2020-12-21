# Built-in

## Built-in types

Alt-Ergo's native language includes the following built-in types.
Creation and manipulation of values having those types are covered in [built-in operators](#built-in-operators).

### Boolean types
 * `bool`, the preferred type to represent propositional variables. Boolean constants are `true` and `false`.
 * `prop`, an historical type still supported in Alt-Ergo 2.3.0.  
    The historical separation comes from Alt-Ergo origins in the Coq ecosystem: in Coq, `prop` is much richer than `bool`.  
    In Alt-Ergo 2.3.0, `prop` and `bool` have been merged in order to simplify interactions with the [SMT-LIB ](http://smtlib.cs.uiowa.edu/) standard.  
    More information on the `bool`/`prop` conflict can be found in [this section](#the-bool-prop-conflict).

### Numeric types
 * `int` for (arbitrary large) integers.
 * `real` for reals. This type actually represents the smallest extension of the rationals which is algebraically closed and closed by exponentiation. Rationals with arbitrary precision are used under the hood. 

### Unit type
 `unit` is Alt-Ergo native language's [unit type](https://en.wikipedia.org/wiki/Unit_type).

### Bitvectors
 `bitv` are fixed-size binary words of arbitrary length.
 There exists a bitvector type `bitv[n]` for each non-zero positive integer `n`. For example, `bitv[8]` is a bitvector of length `8`.

### Type variables
 Alt-Ergo's native language's type system supports prenex polymorphism. This allows efficient reasoning about generic data structure.
 Type variables can be created implicitly, and are implicitly universally quantified in all formulas. Any formula which requires a type can accept a type variable.
 Type variable may be used to parametrize datatypes, as we will see when we will create new types, or in the following example of `farray`.
 
 Type variables are indicated by an apostrophe `'`. For example, `'a` is a type variable.

### Polymorphic functional arrays
 Alt-Ergo's native language includes functional polymorphic arrays, represented by the `farray` type, and has a built-in theory to reason about them.

 The `farray` is parametrized by two types: the type of their indexes (default is `int`) and the type of their values (no default).
 Array can be accessed using any index of valid type.
 Functional polymorphic arrays are persistent structures: they may be updated, but only for the scope of an expression.
 

## Built-in operators

### Logical operators

| Operation    | Notation  | Type(s)              |
|--------------|-----------|----------------------|
| Negation     | `not p`   | `bool -> bool`       |
| Conjonction  | `p and q` | `bool, bool -> bool` |
| Disjonction  | `p or q`  | `bool, bool -> bool` |
| Implication  | `p -> q`  | `bool, bool -> bool` |
| Equivalence  | `p <-> q` | `bool, bool -> bool` |
| Exclusive or | `p xor q` | `bool, bool -> bool` |

For all those operators, `bool` and `prop` are fully interchangeable.

#### The `bool`/`prop` conflict

Prior to Alt-Ergo 2.3.0, Alt-Ergo's native language handled differently boolean variables `bool` and propositional variables `prop`.
The two keywords still exist in Alt-Ergo 2.3.0, but those two types have been made fully compatible: any function or operator taking a `bool` or a `prop` as an argument accepts both.

The historical separation comes from Alt-Ergo origins in the Coq ecosystem: in Coq, `prop` is much richer than `bool`. 
In Alt-Ergo 2.3.0, `prop` and `bool` have been merged in order to simplify interactions with the [SMT-LIB ](http://smtlib.cs.uiowa.edu/) standard.

Note that `bool` can be used in more syntactic constructs than `prop`.
* `prop` **cannot** be the input or output type of a *interpreted function* (`function` keyword), whereas `bool` can.
* `prop` **cannot** be used in the *declaration of new types* (`type` keyword), whereas `bool` can.
* `prop` **cannot** be used as the value of a type variable, whereas `bool` can.
* `prop` **cannot** be the input of an *uninterpreted function* (`logic` keyword), whereas `bool` can.
In all other cases, it is advised the use `prop` rather than `bool`, because it is better handled internally by Alt-Ergo. However, using `bool` would be correct.
* `prop` and `bool` **can** be the output type of an *uninterpreted function* (`logic` keyword).
* `prop` and `bool` **can** be the type of an *uninterpreted variable* (`logic` keyword).
Note that a `predicate` has `prop` output type.

#### Examples

```
(* Correct example *)
logic A,B,C: prop
axiom a1: A -> B
axiom a2: B -> C
goal g: (B->A) and (C->B) -> (A <-> C)
```

```
(* Equivalent example using bool *)
logic A,B,C: bool
axiom a1: A -> B
axiom a2: B -> C
goal g: (B->A) and (C->B) -> (A <-> C)
```

### Numeric operators

| Operation               | Notation  | Type(s)                                                                                        |
|-------------------------|-----------|------------------------------------------------------------------------------------------------|
| Unary negative          | `-x`      | `int -> int`, <br>`real -> real`                                                               |
| Addition                | `x + y`   | `int, int -> int`, <br>`real, real -> real`                                                    |
| Subtraction             | `x - y`   | `int, int -> int`, <br>`real, real -> real`                                                    |
| Multiplication          | `x * y`   | `int, int -> int`, <br>`real, real -> real`                                                    |
| Division                | `x / y`   | `int, int -> int`, <br>`real, real -> real`                                                    |
| Remainder               | `x % y`   | `int, int -> int`                                                                              |
| Exponentiation (`int`)  | `x ** y`  | `int, int -> int`                                                                              |
| Exponentiation (`real`) | `x **. y` | `real, real -> real`, <br>`real, int -> real`, <br>`int, real -> real`, <br>`int, int -> real` |

### Comparisons

| Operation                | Notation                      | Type(s)                                  | Notes                                                                                                            |
|------------------------- |-------------------------------|------------------------------------------|------------------------------------------------------------------------------------------------------------------|
| Equality                 | `x = y`                       | `'a, 'a -> bool`                         | `'a` can be any type                                                                                             |
| Inequality               | `x <> y`                      | `'a, 'a -> bool`                         | Syntactic sugar for `not(x = y)`                                                                                 |
| All distinct             | `distinct(x1,x2,x3, ..., xn)` | `'a, 'a, ..., 'a -> bool`                | Can be used on any number of operands. <br> Syntactic sugar for  `(x1<>x2) and ... and (x1<>xn) and (x2<>x3) and ...` |
| Strictly less than       | `x < y`                       | `int, int -> bool`, <br>`real, real -> bool` |                                                                                                                  |
| Lesser than or equal to  | `x <= y`                      | `int, int -> bool`, <br>`real, real -> bool` |                                                                                                                  |
| Strictly greater than    | `x > y`                       | `int, int -> bool`, <br>`real, real -> bool` |                                                                                                                  |
| Greater than or equal to | `x >= y`                      | `int, int -> bool`, <br>`real, real -> bool` |                                                                                                                  |

Note that binary comparisons operators can be chained: if `op1`, `op2`, ... are binary comparisons operators, than `x0 op1 x1 op2 x2 ...` has the same semantic as `(x0 op1 x1) and (x1 op2 x2) and ...`.

One use of this is the creation of intervals, as in the following example.

```
(* Linear arithmetic over integers *)
goal g:
    forall x,y,z,t:int.
    0 <= y + z <= 1  ->
    x + t + y + z = 1 ->
    y + z <> 0 ->
    x + t = 0
```

### Bitvectors

Remember that bitvectors are fixed-size binary words: vectors of `0` and `1`.

There exists a bitvector type `bitv[n]` for each fixed non-zero positive integer `n`. For example, `bitv[8]` is a bitvector.

Note that bitvectors are indexed from right to left.

| Operation                     | Notation                                                             | Type                          |
|-------------------------------|----------------------------------------------------------------------|-------------------------------|
| Explicit declaration          | `[|<x>|]` <br> where `<x>` is a string of `0` and `1` without spaces | `bitv[<len(x)>]`              |
| Concatenation                 | `x @ y`                                                              | bitv[n], bitv[m] -> bitv[n+m] |
| Extraction of contiguous bits | `x^{p,q}` <br> where 0<=p<=q<len(x)                                  | `bitv[q-p+1]`                 |


#### Examples

```
(** Usage of bitv types *)
logic register: bitv[8]

(** Explicit declaration *)
axiom a: register = [|00101010|]

(** Concatenation 
        Both goals are valid *)
goal g1:
    forall x,y:bitv[16]. x@y=y@x -> x = y

goal g2:
    forall x,y:bitv[3]. x@[|101|] = [|000101|] -> x=[|000|]
    
(** Extraction of contiguous bits *
        All goals are valid)
goal g3:
    [|010|]^{0,1}=[|1100|]^{1,2}

goal g4:
    forall x:bitv[4]. forall y:bitv[2].
    x=y@[|10|] ->
    x^{2,3}=[|11|] ->
    x=[|1110|]

goal g5 : 
    forall x:bitv[32]. forall y:bitv[32]. forall s:bitv[32]. 
    s = y^{0,15} @ x^{16,31} ->
    (s^{16,31} = y^{0,15} and s^{0,15} = x^{16,31}) 
```

### Type variables

As type variables and polymorphism have already been described, let's just look at the following example.

```
logic f: 'a->'b
logic g: 'b->'b

axiom a1: forall x:'a.  g(f(x))=f(x)
axiom a2: forall x:int. f(x)=0

goal g1: 
   (* Valid *)
   g(f(0.01)) = f(0.01)

goal g2: 
   (* Valid *)
   g(f(1)) = g(0)

goal g3: 
   (* I don't know *)
   g(f(0.01)) = g(0)
```

### Polymorphic functional arrays

[TODO: add table?]

Remember that `farray` are parametrized by two types: the type of their indexes (default is `int`) and the type of their values (no default).

#### Syntax
```
(* Instantiation of a farray type *)
<farray_type>        ::= <value_type> 'farray'
                       | '(' <index_type> ',' <value_type> ')' 'farray'

(* Access - this expression is of type (value_type) *)
<farray_access_expr> ::= <array_id> '[' <index> ']'

(* Update - this expression is of type ((index_type) (value_type) farray) *)
<farray_update_expr> ::= <array_id> '[' <index> '<-' <new_value> ( ',' <index> '<-' <new_value> )* ']'
```

#### Examples
```
(* arr1 is a general polymorphic farray *)
logic arr1: ('a, 'b) farray
(* arr2 is a polymorphic farray whose indexes are int *)
logic arr2: 'b farray
(* arr3 is a farray whose indexes are int and whose values are real *)
logic arr3: real farray
(* arr4 is a farray whose indexes are parametrized by 'a and whose values are real *)
logic arr4: ('a, real) farray
(* arr5 is a farray whose indexes and values are real *)
logic arr5: (real, real) farray
```

```
(* Accessing and updating farrays *)
goal g1:
    forall i,j,k:int.
    forall v,w:'a.
    forall b:'a farray.
    b = b[j<-b[i],k<-w] ->
    i = 1 -> j = 2 -> k = 1 ->
    b[i] = b[j]
```

```
(* Using farrays with custom types for indexes and values *)
type t  = A | B | C | D
type t2 = E | F | G | H

goal g2:
    forall a : (t,t2) farray.
    a[B <- E][A] <> E ->
    a[C <- F][A] <> F ->
    a[D <- G][A] <> G ->
    a[A] = H
```
