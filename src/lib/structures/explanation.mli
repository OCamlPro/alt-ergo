(******************************************************************************)
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
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

(** {1 Types} *)

type t
(** Type of a explanation. More precisely, an explanation is a set of reason
    of type {!type:reason}. *)

type rootdep = { name : string; f : Expr.t; loc : Loc.t}

type reason =
  | Literal of Satml_types.Atom.atom
  | Fresh of int
  | Bj of Expr.t
  (** Backjump reason produced by the SAT solvers. *)

  | Dep of Expr.t
  | RootDep of rootdep
  (** Type of reason of an explanation. *)

exception Inconsistent of t * Expr.Set.t list

(** {1 Constructors} *)

val empty : t
(** Trivial explanation. *)

val singleton : reason -> t
(** [singleton rn] produces an explanations whose the only reason is
    [rn]. *)

val is_empty : t -> bool
(** [is_empty ex] is [true] if and only if [ex] is the trivial explanation. *)

val mem : reason -> t -> bool
(** [mem rn ex] check if the reason [rn] is in the explanation [ex]. *)

val union : t -> t -> t
(** [union ex1 ex2] produce the union of the set of explanations [ex1] and
    [ex2]. *)

(* TODO: check the implementation of this function. *)
val merge : t -> t -> t

val iter_atoms : (reason -> unit)  -> t -> unit

val fold_atoms : (reason -> 'a -> 'a )  -> t -> 'a -> 'a

val fresh_reason : unit -> reason
(** [fresh_reason ()] produces a fresh reason. *)

val exists_fresh : t -> bool
(** Does there exists a [Fresh _] reason in the explanation. *)

val remove_fresh : reason -> t -> t option

val remove : reason -> t -> t
(** [remove rn ex] removes the reason [rn] of the explanation [ex]. *)

val add_fresh : reason -> t -> t

val pp : Format.formatter -> t -> unit
(** [pp fmt ex] pretty prints the explanation [ex] on the formatter [fmt]. *)

val print : Format.formatter -> t -> unit
(** Alias of pp used by OcplibSimplex. *)

val get_unsat_core : t -> rootdep list

val print_unsat_core : ?tab:bool -> Format.formatter -> t -> unit

val formulas_of : t -> Expr.Set.t

val bj_formulas_of : t -> Expr.Set.t

(* TODO: move this module in Util. *)
module MI : Map.S with type key = int

val literals_ids_of : t -> int MI.t

val make_deps : Expr.Set.t -> t
(** [make_deps lst] produce an explanation whose the reasons are
    backjump kind. *)

val has_no_bj : t -> bool
(** [has_no_bj ex] is [true] if and only if [ex] contains no reason of
    backjump kind. *)

val compare : t -> t -> int
(** [compare ex1 ex2] compare two explanation [ex1] and [ex2]. *)

val subset : t -> t -> bool
(** [subset ex1 ex2] return [true] if and only if the explanation [ex1]
    is weaker than the explanation [ex2]. *)
