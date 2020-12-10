
# Setting goals

Declaring goals tells Alt-Ergo what it needs to prove.
Alt-Ergo will answer `Valid` if it can prove that the formula of the goal is true in all cases, and `I don't know` otherwise.

## `goal`

To declare goals, the user can use the following construct.
Note that goals must always be named.

#### Syntax
```
<goal_declaration> ::= 'goal' <id> ':' <goal_body>
```
Here, `<goal_body>` is an expression which may contain quantifiers.

#### Examples
```
logic h, g, f: int, int -> int
logic a, b:int

goal g_1:
    h(g(a,a),g(b,b)) = g(b,b) ->
    a = b ->
    g(f(h(g(a,a),g(b,b)),b) - f(g(b,b),a),
      f(h(g(a,a),g(b,b)),a) - f(g(b,b),b)) = g(0,0)
``` 

```
goal g:
  forall x,y:int.
  x > 3 ->
  y = (x + 1) / 2 ->
  x < (y + 1) * (y + 1)
```

## Intermediate goals: `cut` and `check`

`cut` and `check` can be used to create intermediate goals, to check that they can be proven, without using the terms that they generate as known terms for other triggers.
In other word, `cut` and `check` allow to test if intermediate goals can be proven, without having any influence whatsoever on the behaviour of Alt-Ergo on other goals.

`cut` and `check` seem to not be supported by Alt-Ergo 2.3.0 (but those keywords are still reserved).

[WIP: complete]

#### Syntax
```
<check_declaration> ::= 'check' <expr>
<cut_declaration>   ::= 'cut' <expr>
```
 
