# User-defined types

By using the command `type`, the user can declare its own types.

## Abstract types

It is possible to create new uninterpreted types.
They may be parametrized by one or several type variables, or be left non-parametrized.

### Syntax
```
<abstract_type_declaration>    ::= 'type' ( <type_variable> | <type_variable_list_sep_comma> )? <type_id>
<type_variable_list_sep_comma> ::= '(' <type_variable> ( ',' <type_variable> )* ')'
```

### Examples
```
(* New non-parametrized uninterpreted type *)
type person
logic Alice, Bob: person
```

```
(* New type parametrized by one type variable *)
type 'a list

logic integer_lst: int list
logic boolean_lst: bool list
logic polymorphic_lst: 'a list
```

```
(* New type parametrized by several type variables *)
type ('a, 'b, 'c) t
```

```
(* Axioms may be used to put constraints on user-defined types *)
type t
type list

logic nil: list
logic cons: t, list -> list

logic hd: list -> t
logic tl: list -> list

axiom hd_cons: forall x:t. forall l:list. hd (cons(x,l)) = x
axiom tl_cons: forall x:t. forall l:list. tl (cons(x,l)) = l

goal g:
    forall x,y:t. hd(tl(cons(x, cons(y, nil)))) = y
```

```
(* Another example on constraints on user-defined types, this time using polymorphism *)
type 'a set

logic empty: 'a set
logic add: 'a, 'a set -> 'a set
logic mem: 'a, 'a set -> prop

axiom mem_empty:
    forall x: 'a.
    not mem(x, empty: 'a set)

axiom mem_add:
    forall x, y: 'a. forall s: 'a set.
    mem(x, add(y, s)) <-> (x = y or mem(x, s))

logic is1, is2: int set
logic iss: int set set

goal g:
    is1 = is2 ->
    (not mem(1, add(2+3, empty : int set))) and
    mem (is1, add (is2, iss))
```

## Records

One way to create new types with structure is to create records.
They hold several fields, which be accessed.

### Syntax
```
(* Declaration of records *)
<record_type_declaration>      ::= 'type' ( <type_variable> | <type_variable_list_sep_comma> )? <type_id> '=' <record_type>
<type_variable_list_sep_comma> ::= '(' <type_variable> ( ';' <type_variable> )* ')'
<record_type>                  ::= '{' <field_def> ( ',' <field_def> )* '}'
<field_def>                    ::= <field_id> ':' <field_type>

(* Access *)
<record_access_expr>           ::= <record_id> '.' <field_id>

(* Inline record declaration *)
<record_value>                 ::= '{' <field_value> ( ',' <field_value> )* '}'
<field_value>                    ::= <field_id> '=' <value>
```

### Examples
```
type sa_family_t

type sockaddr = {
    sa_len:    int;
    sa_family: sa_family_t;
    sa_data:   bitv[112]
}

logic sa:     sockaddr
axiom sa_len: sa.sa_len = 8
```

```
type 'a pair = {fst : 'a ; snd : 'a}
type elt
  
goal g7:
    forall x,y:int. {fst=x; snd=y}.
    fst + 1 = 2 -> x=1
```

## Enums and Algebraic datatypes

Algebraic datatypes (ADT) are a very powerful tool which allows Alt-Ergo to reason about generic, recursive data structures.

It is possible to create enumerations, and to use records in order to construct (mutually) recursive structures and to add additionnal structures.

### Examples

 - When no recursion is involved, we usually talk of *enumerations*, or simply *enums*, which are the simplest examples of ADT.

    *Example:* 
    ```
    type poker_suit = diamond | club | heart | spade
    ```
   
 - Records may be used in ADT to give additionnal structure.

    *Example:* 
    ```
    type 'a and_infty = infty | number of { x:'a }
    ```
   
 - More complex examples involve recursion.

    *Example:* 
    ```
    type nat = zero | succ of { x:nat }

    logic one,two,three:nat
    axiom a: one = succ(zero) and two = succ(one) and three = succ(two)
    ```

 - ADT may be parametrized.

    *Example:* 
    ```
    type 'a tree = NIL | Node of { left:'a tree; val:'a; right:'a tree }
    ```

 - It is possible to define mutually recursive structures by using the keyword `and`.

    *Example:*
    ```
    type  'a tree   = Empty | Node of { val:'a; children:'a forest }
    and   'a forest = Nil   | Cons of { head:'a tree; tail:'a forest }
    ```

 - ADT can be used like any type. Constructors can be called just as functions (if they are defined as records) or as constants (otherwise).
    *Example:*
    ```
    type 'a tree = NIL | Node of { left:'a tree; val:'a; right:'a tree }
    logic t:int tree
    axiom a: t= Node(Node(NIL,2,Node(NIL,3,NIL)),1,NIL)
    ```

### Syntax
```
(* Declaration of ADT *)
<algebraic_type_declaration>   ::= 'type' <algebraic_type_definition> ( 'and' <algebraic_type_definition> )*
<algebraic_type_definition>    ::= ( <type_variable> | <type_variable_list_sep_comma> )? <type_id> '=' <abstract_type>
<type_variable_list_sep_comma> ::= '(' <type_variable> ( ';' <type_variable> )* ')'
<abstract_type>                ::= <constr> ( '|' <constr> )*
<constr>                       ::= <id> ( 'of' <record_type> )?
<record_type>                  ::= '{' <field> ( ',' <field> )* '}'
<field>                        ::= <field_id> ':' <field_type>

(* ADT usage *)
(* TODO *)
``` 

Values of ADT can be created through the ADT's constructors, with the same syntax as functions.
