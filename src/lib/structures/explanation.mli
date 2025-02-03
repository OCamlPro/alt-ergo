(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type t

type rootdep = { name : string; f : Expr.t; loc : Dolmen.Std.Loc.loc}

type exp =
  | Literal of Satml_types.Atom.atom
  | Fresh of int
  | Bj of Expr.t
  | Dep of Expr.t
  | RootDep of rootdep

exception Inconsistent of t * Expr.Set.t list

val empty : t

val is_empty : t -> bool

val mem : exp -> t -> bool

val singleton : exp -> t

val union : t -> t -> t

val merge : t -> t -> t

val iter_atoms : (exp -> unit)  -> t -> unit

val fold_atoms : (exp -> 'a -> 'a )  -> t -> 'a -> 'a

val fresh_exp : unit -> exp

val exists_fresh : t -> bool
(** Does there exists a [Fresh _] exp in an explanation set. *)

val remove_fresh : exp -> t -> t option

val remove : exp -> t -> t

val add_fresh : exp -> t -> t

val print : Format.formatter -> t -> unit

val get_unsat_core : t -> rootdep list

val print_unsat_core : ?tab:bool -> Format.formatter -> t -> unit

val formulas_of : t -> Expr.Set.t

val bj_formulas_of : t -> Expr.Set.t

module MI : Map.S with type key = int

val make_deps : Expr.Set.t -> t

val has_no_bj : t -> bool

val compare : t -> t -> int

val subset : t -> t -> bool
