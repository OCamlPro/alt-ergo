Expériences menées sur z3, cvc4 et alt-ergo pour la génération de modèle en cas de SAT

- z3 : `z3 fichier.smt2`
  - le fichier doit contenir `(get-model)` après chaque `(check-sat)` dont on veut un modèle
  - l'option `produce-models` doit être à `true` (comportement par défaut) et peut l'être avec la commande `(set-option :produce-models true)`
- cvc4 : `cvc4 --produce-models fichier.smt2`
- alt-ergo :
  - `alt-ergo -mdefault --sat-solver Tableaux fichier.smt2` (fonctionne uniquement si les termes sont étiquetés par `"model:"` mais n'affiche que le dernier terme étiqueté, visiblement)
  - `alt-ergo -mcomplete --sat-solver Tableaux fichier.smt2` (affiche le premier modèle complet trouvé)
  - `alt-ergo -mall --sat-solver Tableaux fichier.smt2` (affiche l'ensemble des modèles complets trouvés, déclenche une assertion failure de temps en temps)
  - `alt-ergo --interpretation 1 --sat-solver Tableaux fichier.smt2` (déclenche un calcul de modèle et l'affiche à la fin de l'exécution)
  - `alt-ergo --interpretation 2 --sat-solver Tableaux fichier.smt2` (déclenche un calcul de modèle à chaque tour d'instantiation d'axiome)
  - `alt-ergo --interpretation 3 --sat-solver Tableaux fichier.smt2` (déclenche un calcul de modèle à chaque décision booléenne dans le solveur SAT)

Premier exemple:

```
(set-logic QF_UF)
(set-option :produce-models true) ; enable model generation
(declare-const p Bool)
(declare-const q Bool)
(assert (!(=> (not p) q) :named ass1))
(check-sat)
(get-model)
(exit)
```

`z3 examples/smt2/bool/bool1.smt2` :

```
sat
(model
  (define-fun p () Bool
    false)
  (define-fun q () Bool
    true)
)
```

`cvc4 examples/smt2/bool/bool1.smt2` :

```
sat
(model
(define-fun p () Bool false)
(define-fun q () Bool true)
(define-fun ass1 () Bool true)
)
```

`./alt-ergo examples/smt2/bool/bool1.smt2 --sat-solver Tableaux -mcomplete`

```
;[Warning] (set-option not yet supported)
;[Warning] (get-model not yet supported)
; File "examples/smt2/bool/bool1.smt2", line 6, characters 1-12:I don't know (0.0072) (1 steps) (goal g)
unknown

Model

Propositional:
 true
 p

Theory:
 p = FT:[true]
 true <> false

Relation:
```

`./alt-ergo examples/smt2/bool/bool1.smt2 --sat-solver Tableaux -mall`

```
;[Warning] (set-option not yet supported)
;[Warning] (get-model not yet supported)
--- SAT model found ---
 true
 p
--- / SAT model  ---
--- SAT model found ---
 true
 q
 (not p)
--- / SAT model  ---
Fatal error: exception File "src/lib/reasoners/fun_sat.ml", line 1641, characters 6-12: Assertion failed
```

`z3 examples/smt2/uf/uf1.smt2` :

```
sat
(model
  (define-fun a () Int
    21)
  (define-fun b () Int
    22)
  (define-fun f ((x!0 Int)) Int
    1)
)
```

`./alt-ergo examples/smt2/uf/uf1.smt2 --sat-solver Tableaux -mcomplete`
```
;[Warning] (get-model not yet supported)
; File "examples/smt2/uf/uf1.smt2", line 7, characters 1-12:I don't know (0.0072) (3 steps) (goal g)
unknown

Model

Propositional:
 true
 (1 = f(10))
 (a <= (b - 1))
 (20 <= (a - 1))

Theory:
 f(10) = X1(arith):[1 [int]]
 true <> false

Relation:
```

`./alt-ergo examples/smt2/uf/uf1.smt2 --sat-solver Tableaux -mall`

```
;[Warning] (get-model not yet supported)
--- SAT model found ---
 true
 (1 = f(10))
 (a <= (b - 1))
 (20 <= (a - 1))
--- / SAT model  ---
; File "examples/smt2/uf/uf1.smt2", line 7, characters 1-12:I don't know (0.0057) (3 steps) (goal g)
unknown
```

`z3 examples/smt2/array/array1.smt2`

```
sat
(model
  (define-fun y () Int
    0)
  (define-fun a1 () (Array Int Int)
    (store ((as const (Array Int Int)) 1) 0 0))
  (define-fun x () Int
    0)
  (define-fun z () Int
    0)
  (define-fun a2 () (Array Int Int)
    ((as const (Array Int Int)) 0))
  (define-fun a3 () (Array Int Int)
    ((as const (Array Int Int)) 0))
)
```

`./alt-ergo examples/smt2/array/array1.smt2 --sat-solver Tableaux -mcomplete`

```
;[Warning] (get-model not yet supported)
; File "examples/smt2/array/array1.smt2", line 9, characters 1-12:I don't know (0.0072) (3 steps) (goal g)
unknown

Model

Propositional:
 true
 (a1 = a1[x<-y])
 (x = a1[x])

Theory:
 a1[x<-y][x] = a1[x] = x = FT:[y]
 a1[x<-y] = FT:[a1]
 true <> false

Relation:
 a1[x<-y][x] ∈ ]-inf;+inf[
 a1[x] ∈ ]-inf;+inf[
 x ∈ ]-inf;+inf[
 y ∈ ]-inf;+inf[
```

`./alt-ergo examples/smt2/array/array1.smt2 --sat-solver Tableaux -mall`


```
;[Warning] (get-model not yet supported)
--- SAT model found ---
 true
 (a1 = a1[x<-y])
 (x = a1[x])
--- / SAT model  ---
; File "examples/smt2/array/array1.smt2", line 9, characters 1-12:I don't know (0.0067) (3 steps) (goal g)
unknown
```
