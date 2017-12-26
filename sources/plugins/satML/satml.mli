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

module Types : sig

  type atom
  type var
  type clause

  val pr_atom : Format.formatter -> atom -> unit
  val pr_clause : Format.formatter -> clause -> unit
  val get_atom : Literal.LT.t ->  atom

  val literal : atom -> Literal.LT.t
  val weight : atom -> float
  val is_true : atom -> bool
  val neg : atom -> atom
  val vrai_atom  : atom
  val faux_atom  : atom
  val level : atom -> int
  val index : atom -> int
  val cmp_atom : atom -> atom -> int
  val eq_atom : atom -> atom -> bool
  val reason_atoms : atom -> atom list
(*
  type var
  type reason
  type premise

(*module Make (Dummy : sig end) : sig*)

  val neg : atom -> atom

  val cpt_mk_var : int ref
  val ma : var Literal.LT.Map.t ref

  val dummy_var : var
  val dummy_atom : atom
  val dummy_clause : clause

  val make_var : Literal.LT.t -> var * bool

  val add_atom : Literal.LT.t -> atom
  val vrai_atom  : atom
  val faux_atom  : atom

  val make_clause : string -> atom list -> Formula.t -> int -> bool ->
  premise-> clause

  val fresh_name : unit -> string

  val fresh_lname : unit -> string

  val fresh_dname : unit -> string

  val to_float : int -> float

  val to_int : float -> int
  val made_vars_info : unit -> int * var list
  val clear : unit -> unit

(****)

  val eq_atom   : atom -> atom -> bool
  val hash_atom  : atom -> int
  val tag_atom   : atom -> int

  val cmp_var : var -> var -> int
  val eq_var   : var -> var -> bool
  val h_var    : var -> int
  val tag_var  : var -> int

(*end*)

*)
end


(******************************************************************************)

module Flat_Formula : sig

  type t
  type view = private UNIT of Types.atom | AND of t list | OR of t list

  val print   : Format.formatter -> t -> unit

  val view    : t -> view
  val vrai    : t
  val faux    : t

  val mk_lit  : Literal.LT.t -> Types.var list -> t * Types.var list
  val mk_not  : t -> t
  val mk_and  : t list -> t
  val mk_or   : t list -> t

  val compare : t -> t -> int
  val equal   : t -> t -> bool

  val simplify :
    Formula.t ->
    (Formula.t -> t * 'a) ->
    Types.var list ->
    t * (Formula.t * (t * Types.atom)) list
      * Types.var list

  val cnf_abstr : t ->
    (Types.atom * Types.atom list * bool) Util.MI.t ->
    Types.var list ->
    Types.atom
    * (Types.atom * Types.atom list * bool) list
    * (Types.atom * Types.atom list * bool) Util.MI.t
    * Types.var list

  val expand_proxy_defn :
    Types.atom list list ->
    Types.atom * Types.atom list * bool -> Types.atom list list

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

exception Sat
exception Unsat of Types.clause list option

module type SAT_ML = sig

  (*module Make (Dummy : sig end) : sig*)
  type state
  type th

  val solve : unit -> unit
  val assume :
    Types.atom list list -> Types.atom list list -> Formula.t ->
    Types.var list ->
    (Types.atom * Types.atom list * bool) Util.MI.t -> cnumber : int -> unit

  val boolean_model : unit -> Types.atom list
  val theory_assumed : unit -> (Literal.LT.t * int * int) list list
  val current_tbox : unit -> th
  val set_current_tbox : th -> unit
  val empty : unit -> unit
  val clear : unit -> unit

  val save : unit -> state
  val restore : state -> unit

  val reset_steps : unit -> unit
  val get_steps : unit -> int64

  val assume_th_elt : Commands.th_elt -> unit
  val decision_level : unit -> int
  val cancel_until : int -> unit

  val update_lazy_cnf :
    Types.atom option Flat_Formula.Map.t -> dec_lvl:int -> unit

  val exists_in_lazy_cnf : Flat_Formula.t -> bool
  val known_lazy_formulas : unit -> int Flat_Formula.Map.t

(*end*)
end

module Make (Th : Theory.S) : SAT_ML with type th = Th.t

