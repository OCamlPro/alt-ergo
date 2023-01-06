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
(** Type of a set of explanations. *)

type rootdep = { name : string; f : Expr.t; loc : Loc.t}

type exp =
  | Literal of Satml_types.Atom.atom
  | Fresh of int
  | Bj of Expr.t
  (** Backjump explanation. *)

  | Dep of Expr.t
  | RootDep of rootdep
  (** Type of element of an explanation. *)

exception Inconsistent of t * Expr.Set.t list

(** {1 Constructors} *)

val empty : t
(** Trivial explanation. *)

val singleton : exp -> t
(** [singleton ex] produces an explanation whose the only element is [ex]. *)

val is_empty : t -> bool
(** [is_empty ex] is [true] if and only if [ex] is the trivial explanation. *)

val mem : exp -> t -> bool

val union : t -> t -> t

val merge : t -> t -> t

val iter_atoms : (exp -> unit)  -> t -> unit

val fold_atoms : (exp -> 'a -> 'a )  -> t -> 'a -> 'a

val fresh_exp : unit -> exp

val exists_fresh : t -> bool
(** Does there exists a [Fresh _] exp in an explanation set. *)

val remove_fresh : exp -> t -> t option

val remove : exp -> t -> t
(** [remove exp ex] removes the element [exp] of the explanation [ex]. *)

val add_fresh : exp -> t -> t

val pp : Format.formatter -> t -> unit
(** [pp fmt ex] pretty prints the explanation [ex] on the formatter [fmt]. *)

val print : Format.formatter -> t -> unit
(** Alias of pp used by OcplibSimplex. *)

val get_unsat_core : t -> rootdep list

val print_unsat_core : ?tab:bool -> Format.formatter -> t -> unit

val formulas_of : t -> Expr.Set.t

val bj_formulas_of : t -> Expr.Set.t

module MI : Map.S with type key = int

val literals_ids_of : t -> int MI.t

val make_deps : Expr.Set.t -> t

val has_no_bj : t -> bool

val compare : t -> t -> int
(** [compare ex1 ex2] compares two explanation [ex1] and [ex2]. *)

val subset : t -> t -> bool
