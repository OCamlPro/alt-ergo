 

# Control flow

## `let [...] in`

Like in OCaml, let expressions are available. They allow for named local expressions, which are written `let name = expression in [...]`.
Name defined like this only have local scope.

### Syntax
```
<let_expression>       ::= 'let' <let_binders> 'in' <expr>
<let_binders>          ::= <id> '=' <expr> ( ',' <id> '=' <expr> )*
```

### Example
```
function average(a:real, b:real):real =
    let sum = a+b in
    sum / 2.
```

## `match [...] with`

Pattern matching, a [Really Cool Feature](https://ocaml.org/learn/tutorials/data_types_and_matching.html) present in most functional languages, is available in Alt-Ergo's native language as well.

Warning: the only patterns that can be matched are constructors of algebraic datatypes.
Moreover, constructors can't be nested in a pattern.

### Syntax
```
<match_expr>     ::= 'match' <expr> 'with' <match_cases> 'end'
<match_cases>    ::= '|'? <simple_pattern> '->' <expr> ( '|' <simple_pattern> '->' <expr> )*
<simple_pattern> ::= <id> | <id_application> '(' <args> ')'
<args>           ::= <id> ( "," <id> )*
```

### Example
```
type 'a tree = NIL | Node of { left:'a tree; val:'a; right:'a tree }

function max(a:int, b:int):int =
    if a>b then a else b

function height(t: 'a tree):int =
    match t with
        | NIL         -> 0
        | Node(l,_,r) -> 1 + max(height(l),height(r))
    end
```

## `if [...] then [...] else`

The simple construct `if then else` for conditional expressions is available in Alt-Ergo's native language.

### Syntax
```
<ite_expr>     ::= 'if' <cond_expr> 'then' <branch1_expr> 'else' <branch2_expr>
(* Note that <cond_expr> must have type bool - or prop *)
<cond_expr>    ::= <expr>
(* Note that <branch1_expr> and <branch2_expr> must have same type *)
<branch1_expr> ::= <expr>
<branch2_expr> ::= <expr>
```

### Example
```
function max(a:int, b:int):int =
    if a>b then a else b
```
