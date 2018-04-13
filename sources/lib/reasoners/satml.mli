(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Satml_types

exception Sat
exception Unsat of Satml_types.Atom.clause list option

module type SAT_ML = sig

  (*module Make (Dummy : sig end) : sig*)
  type th
  type t

  val solve : t -> unit

  val set_new_proxies :
    t ->
    (Satml_types.Atom.atom * Satml_types.Atom.atom list * bool) Util.MI.t ->
    unit

  val new_vars :
    t ->
    nbv : int -> (* nb made vars *)
    Satml_types.Atom.var list ->
    Satml_types.Atom.atom list list -> Satml_types.Atom.atom list list ->
    Satml_types.Atom.atom list list * Satml_types.Atom.atom list list

  val assume :
    t ->
    Satml_types.Atom.atom list list ->
    Satml_types.Atom.atom list list ->
    Formula.t ->
    cnumber : int ->
    Satml_types.Atom.atom option Flat_Formula.Map.t -> dec_lvl:int ->
    unit

  val boolean_model : t -> Satml_types.Atom.atom list
  val theory_assumed : t -> Literal.LT.Set.t
  val current_tbox : t -> th
  val set_current_tbox : t -> th -> unit
  val empty : unit -> t

  val reset_steps : unit -> unit
  val get_steps : unit -> int64

  val assume_th_elt : t -> Commands.th_elt -> unit
  val decision_level : t -> int
  val cancel_until : t -> int -> unit

  val update_lazy_cnf :
    t ->
    do_bcp : bool ->
    Satml_types.Atom.atom option Flat_Formula.Map.t -> dec_lvl:int -> unit

  val exists_in_lazy_cnf : t -> Flat_Formula.t -> bool
  val known_lazy_formulas : t -> int Flat_Formula.Map.t

(*end*)
end

module Make (Th : Theory.S) : SAT_ML with type th = Th.t

