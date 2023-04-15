(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) 2013-2023 --- OCamlPro SAS                                  *)
(*                                                                            *)
(*  This file is distributed under the terms of the OCamlPro Non-Commercial   *)
(*  License version 2.0                                                       *)
(*                                                                            *)
(*  AS AN EXCEPTION, Gold members of the Alt-Ergo's Club can distribute this  *)
(*  file under the terms of the Apache Software License version 2             *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(******************************************************************************)


(* Symbols *)


type builtin =
    LE | LT (* arithmetic *)
  | IsConstr of Hstring.t (* ADT tester *)

type operator =
    Plus | Minus | Mult | Div | Modulo
  | Concat | Extract | Get | Set | Fixed | Float
  | Reach | Access of Hstring.t | Record
  | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
  | Sqrt_real_default | Sqrt_real_excess
  | Min_real | Min_int | Max_real | Max_int | Integer_log2
  | Pow | Integer_round
  | Constr of Hstring.t (* enums, adts *)
  | Destruct of Hstring.t * bool
  | Tite

type lit =
  (* literals *)
  | L_eq
  | L_built of builtin
  | L_neg_eq
  | L_neg_built of builtin
  | L_neg_pred

type form =
  (* formulas *)
  | F_Unit of bool
  | F_Clause of bool
  | F_Iff
  | F_Xor
  | F_Lemma
  | F_Skolem

type name_kind = Ac | Other

type bound_kind =
    VarBnd of Var.t
  | ValBnd of Numbers.Q.t

type bound = (* private *)
  { bkind : bound_kind; (* was kind *)
    sort : Ty.t; is_open : bool; is_lower : bool }

type symbol =
  | True
  | False
  | Void
  | Name of Hstring.t * name_kind
  | Int of Hstring.t
  | Real of Hstring.t
  | Bitv of string
  | Op of operator
  | Lit of lit
  | Form of form
  | Var of Var.t
  | In of bound * bound
  | MapsTo of Var.t (* beware: semantic_trigger.MapsTo renamed to SemMapsTo *)
  | Let

module SYMBOL = struct

  let compare_kinds k1 k2 =
    Util.compare_algebraic k1 k2
      (function
        | _, (Ac | Other) -> assert false
      )

  let compare_operators op1 op2 =
    Util.compare_algebraic op1 op2
      (function
        | Access h1, Access h2 | Constr h1, Constr h2 -> Hstring.compare h1 h2
        | Destruct (h1, b1), Destruct(h2, b2) ->
          let c = Stdlib.compare b1 b2 in
          if c <> 0 then c else Hstring.compare h1 h2
        | _ , (Plus | Minus | Mult | Div | Modulo
              | Concat | Extract | Get | Set | Fixed | Float | Reach
              | Access _ | Record | Sqrt_real | Abs_int | Abs_real
              | Real_of_int | Int_floor | Int_ceil | Sqrt_real_default
              | Sqrt_real_excess | Min_real | Min_int | Max_real | Max_int
              | Integer_log2 | Pow | Integer_round
              | Constr _ | Destruct _ | Tite) -> assert false
      )

  let compare_builtin b1 b2 =
    Util.compare_algebraic b1 b2
      (function
        | IsConstr h1, IsConstr h2 -> Hstring.compare h1 h2
        | _, (LT | LE | IsConstr _) -> assert false
      )

  let compare_lits lit1 lit2 =
    Util.compare_algebraic lit1 lit2
      (function
        | L_built b1, L_built b2 -> compare_builtin b1 b2
        | L_neg_built b1, L_neg_built b2 -> compare_builtin b1 b2
        | _, (L_eq | L_built _ | L_neg_eq | L_neg_built _ | L_neg_pred) ->
          assert false
      )

  let compare_forms f1 f2 =
    Util.compare_algebraic f1 f2
      (function
        | F_Unit b1, F_Unit b2
        | F_Clause b1, F_Clause b2 -> Stdlib.compare b1 b2
        | _, (F_Unit _ | F_Clause _ | F_Lemma | F_Skolem
             | F_Iff | F_Xor) ->
          assert false
      )

  let compare_bounds_kind a b =
    Util.compare_algebraic a b
      (function
        | VarBnd h1, VarBnd h2 -> Var.compare h1 h2
        | ValBnd q1, ValBnd q2 -> Numbers.Q.compare q1 q2
        | _, (VarBnd _ | ValBnd _) -> assert false
      )

  let compare_bounds a b =
    let c = Ty.compare a.sort b.sort in
    if c <> 0 then c
    else
      let c = Stdlib.compare a.is_open b.is_open in
      if c <> 0 then c
      else
        let c = Stdlib.compare a.is_lower b.is_lower in
        if c <> 0 then c
        else compare_bounds_kind a.bkind b.bkind

  let compare s1 s2 =
    Util.compare_algebraic s1 s2
      (function
        | Int h1, Int h2
        | Real h1, Real h2 -> Hstring.compare h1 h2
        | Var v1, Var v2 | MapsTo v1, MapsTo v2 -> Var.compare v1 v2
        | Name (h1, k1), Name (h2, k2) ->
          let c = Hstring.compare h1 h2 in
          if c <> 0 then c else compare_kinds k1 k2
        | Bitv s1, Bitv s2 -> String.compare s1 s2
        | Op op1, Op op2 -> compare_operators op1 op2
        | Lit lit1, Lit lit2 -> compare_lits lit1 lit2
        | Form f1, Form f2 -> compare_forms f1 f2
        | In (b1, b2), In (b1', b2') ->
          let c = compare_bounds b1 b1' in
          if c <> 0 then c else compare_bounds b2 b2'
        | _ ,
          (True | False | Void | Name _ | Int _ | Real _ | Bitv _
          | Op _ | Lit _ | Form _ | Var _ | In _ | MapsTo _ | Let) ->
          assert false
      )

  module Set : Set.S with type elt = symbol =
    Set.Make (struct type t=symbol let compare=compare end)

  module Map : sig
    include Map.S with type key = symbol
  end = struct
    include Map.Make (struct type t = symbol let compare = compare end)
  end

end

(** Data structures from Expr *)

type binders = (Ty.t * int) SYMBOL.Map.t (*int tag in globally unique *)

type expr = (* term_view *)
  {
    f: symbol;
    xs: expr list;
    ty: Ty.t;
    bind : bind_kind;
    tag: int;
    vars : (Ty.t * int) SYMBOL.Map.t; (* vars to types and nb of occurences *)
    vty : Ty.Svty.t;
    depth: int;
    nb_nodes : int;
    pure : bool;
    mutable neg : expr option
  }

and decl_kind =
  | Dtheory
  | Daxiom
  | Dgoal
  | Dpredicate of expr
  | Dfunction of expr

and bind_kind =
  | B_none
  | B_lemma of quantified
  | B_skolem of quantified
  | B_let of letin

and quantified = {
  name : string;
  main : expr;
  toplevel : bool;
  user_trs : trigger list;
  binders : binders;
  (* These fields should be (ordered) lists ! important for skolemization *)
  sko_v : expr list;
  sko_vty : Ty.t list;
  loc : Loc.t; (* location of the "GLOBAL" axiom containing this quantified
                  formula. It forms with name a unique id *)
  kind : decl_kind; (* beware: bound.kind was renamed to bkind *)
}

and letin = {
  let_v: symbol;
  let_e : expr;
  in_e : expr;
  let_sko : expr; (* fresh symb. with free vars *)
  is_bool : bool;
}

and semantic_trigger =
  | Interval of expr * bound * bound
  | SemMapsTo of Var.t * expr (* was MapsTo *)
  | NotTheoryConst of expr
  | IsTheoryConst of expr
  | LinearDependency of expr * expr

and trigger = {
  content : expr list;
  (* this field is filled (with a part of 'content' field) by theories
     when assume_th_elt is called *)
  semantic : semantic_trigger list;
  hyp : expr list;
  t_depth : int;
  from_user : bool;
  guard : expr option
}


type subst = expr SYMBOL.Map.t * Ty.subst

type lit_view =
  | Eq of expr * expr
  | Eql of expr list
  | Distinct of expr list
  | Builtin of bool * builtin * expr list
  | Pred of expr * bool

type form_view =
  | Unit of expr * expr  (* unit clauses *)
  | Clause of expr * expr * bool      (* a clause (t1 or t2) bool <-> is implication *)
  | Iff of expr * expr
  | Xor of expr * expr
  | Literal of expr   (* an atom *)
  | Lemma of quantified   (* a lemma *)
  | Skolem of quantified  (* lazy skolemization *)
  | Let of letin (* a binding of an expr *)


type gformula = {
  ff: expr;
  nb_reductions : int;
  trigger_depth : int;
  age: int;
  lem: expr option;
  origin_name : string;
  from_terms : expr list;
  mf: bool;
  gf: bool;
  gdist : int; (* dist to goal *)
  hdist : int; (* dist to hypotheses *)
  theory_elim : bool;
}

type th_elt =
  {
    th_name : string;
    ax_name : string;
    ax_form : expr;
    extends : Util.theories_extensions;
    axiom_kind : Util.axiom_kind;
  }





type 'a ac =
  {h: symbol ; t: Ty.t ; l: ('a * int) list; distribute: bool}


(* bitv *)

type sort_var = A | B | C

type tvar = { var : int ; sorte : sort_var }


(* Shostak *)

type rview =
  | TERM  of expr
  | AC    of r ac
  | ARITH    of polynome
  | RECORDS    of records
  | BITV    of bitv
  | ARRAYS    of arrays
  | ENUM    of enum
  | ADT    of adt
  | ITE    of ite

and r = {v : rview ; id : int}

and polynome = { m : (r, Numbers.Q.t) CMap.map;
                 c : Numbers.Q.t;
                 pty : Ty.t }

and adt = (* was r Adt.abstract *)
  | Constr of { c_name : Hstring.t ; c_ty : Ty.t ; c_args : (Hstring.t * r) list }
  | Select of { d_name : Hstring.t ; d_ty : Ty.t ; d_arg : r }
  | Tester of { t_name : Hstring.t ; t_arg : r } (* tester is currently not used *)
  | Alien of r

and records = (* was Records.abstract *)
  | Record of (Hstring.t * records) list * Ty.t
  | Access of Hstring.t * records * Ty.t
  | ROther of r * Ty.t (* was Other *)

(* bitv *)
and xterm =
  | BVVar of tvar (* was Var *)
  | BVAlien of r (* was Alien *)

and 'a alpha_term = {
  bv : 'a;
  sz : int;
}

and simple_term_aux =
  | Cte of bool
  | BVOther of xterm (* was Other *)
  | Ext of xterm * int * int * int (*// id * size * i * j //*)

and simple_term = simple_term_aux alpha_term

and bitv =  simple_term list

(* was Arrays.abstract *)
and arrays = unit (* why ? *)

(* was Enum.abstract *)
and enum =
    Cons of Hstring.t * Ty.t
  | EAlien of r (* was Alien *)

(* was Ite.abstract *)
and ite = unit (* why ? *)



(* for the solver *)

type solver_simple_term_aux =
  | S_Cte of bool
  | S_Var of tvar

type solver_simple_term = solver_simple_term_aux alpha_term

type t
