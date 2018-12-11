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

type t

type exp =
  | Literal of Satml_types.Atom.atom
  | Fresh of int
  | Bj of Expr.t
  | Dep of Expr.t
  | RootDep of string (* name of the toplevel formula *)

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

val remove_fresh : exp -> t -> t option

val remove : exp -> t -> t

val add_fresh : exp -> t -> t

val print : Format.formatter -> t -> unit

val print_unsat_core : ?tab:bool -> Format.formatter -> t -> unit

val formulas_of : t -> Expr.Set.t

val bj_formulas_of : t -> Expr.Set.t

module MI : Map.S with type key = int

val literals_ids_of : t -> int MI.t

val make_deps : Expr.Set.t -> t

val has_no_bj : t -> bool

val compare : t -> t -> int

val subset : t -> t -> bool
