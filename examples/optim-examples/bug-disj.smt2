logic m1, m2, ae : prop
logic x, y : int

axiom a1:
 x = if ae then 0 else 1

axiom a2:
 y = if (m1 or m2) then 0 else 1

goal g:
 minimize(x + y, 1) ->
 false