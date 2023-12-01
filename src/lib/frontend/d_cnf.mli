(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

val clear_cache : unit -> unit
(** Empties the internal cache of the module. *)

val dty_to_ty : ?update:bool -> ?is_var:bool -> D_loop.DStd.Expr.ty -> Ty.t
(** [dty_to_ty update is_var subst tyv_substs dty]

    Converts a Dolmen type to an Alt-Ergo type.
    - If [update] is [true] then for each type variable of type [DE.Ty.Var.t],
      if it was not encountered before, a new type variable of type [Ty.t] is
      created and added to the cache.
    - If [dty] is a type application, or an arrow type, only its return type
      is converted since those have no counterpart in AE's [Ty] module. The
      function arguments' types or the type paramters ought to be converted
      individually.
*)

(** [make_defs dlist loc]
    Transforms the dolmen definition list [dlist] into an Alt-Ergo definition.
    Dolmen definitions can be:
    - Definitions, that either are predicates (transformed in `PredDef) or
      simple definitions (transformed in `Assume);
    - Type aliases (filtered out);
    - Statements used in models (they must not be in the input list, otherwise
      this function fails). *)
val make_defs :
  D_loop.Typer_Pipe.def list ->
  Loc.t ->
  [> `Assume of string * Expr.t  | `PredDef of Expr.t * string ] list

(** [make_expr ~loc ~name_base ~toplevel ~decl_kind term]

    Builds an Alt-Ergo hashconsed expression from a dolmen term
*)
val mk_expr :
  ?loc:Loc.t ->
  ?name_base:string ->
  ?toplevel:bool ->
  decl_kind:Expr.decl_kind -> D_loop.DStd.Expr.term -> Expr.t

(** [make_form name term loc decl_kind]
    Same as `make_expr`, but for formulas. It applies a purification step and
    processes free variables by adding a forall quantifier. *)
val make_form :
  string ->
  D_loop.DStd.Expr.term ->
  Loc.t ->
  decl_kind:Expr.decl_kind ->
  Expr.t

(** Preprocesses the body of a goal by:
    - removing the top-level universal quantifiers and considering their
      quantified variables as uninsterpreted symbols.
    - transforming a given formula: [a[1] -> a[2] -> ... -> a[n]] in which
      the [a[i]]s are subformulas and [->] is a logical implication, to a set of
      hypotheses [{a[1]; ...; a[n-1]}], and a goal [a[n]] whose validity is
      verified by the solver.
      If additional hypotheses are provided in [hyps], they are preprocessed and
      added to the set of hypotheses in the same way as the left-hand side of
      implications. In other words, [pp_query ~hyps:[h1; ...; hn] t] is the same
      as [pp_query (h1 -> ... -> hn t)], but more convenient if the some
      hypotheses are already separated from the goal.
      Returns a list of hypotheses and the new goal body
*)
val pp_query :
  ?hyps:D_loop.DStd.Expr.term list ->
  D_loop.DStd.Expr.term ->
  D_loop.DStd.Expr.term list * D_loop.DStd.Expr.term

(** Registers the declarations in the cache. If there are more than one element
    in the list, it is assumed they are mutually recursive (but if it is not the
    case, it still work). *)
val cache_decls : D_loop.Typer_Pipe.decl list -> unit

val builtins :
  Dolmen_loop.State.t ->
  D_loop.Typer.lang ->
  Dolmen_loop.Typer.T.builtin_symbols

val is_pure_term : Expr.t -> bool
