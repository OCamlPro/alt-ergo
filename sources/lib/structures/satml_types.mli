(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)


module type ATOM = sig

  type var =
    {  vid : int;
       pa : atom;
       na : atom;
       mutable weight : float;
       mutable sweight : int;
       mutable seen : bool;
       mutable level : int;
       mutable index : int;
       mutable reason: reason;
       mutable vpremise : premise}

  and atom =
    { var : var;
      lit : Expr.t;
      neg : atom;
      mutable watched : clause Vec.t;
      mutable is_true : bool;
      mutable timp : int;
      aid : int }

  and clause =
    { name : string;
      mutable atoms : atom Vec.t ;
      mutable activity : float;
      mutable removed : bool;
      learnt : bool;
      cpremise : premise;
      form : Expr.t}

  and reason = clause option

  and premise = clause list

  type hcons_env

  val empty_hcons_env : unit -> hcons_env
  val copy_hcons_env : hcons_env -> hcons_env
  val nb_made_vars : hcons_env -> int

  val pr_atom : Format.formatter -> atom -> unit
  val pr_clause : Format.formatter -> clause -> unit
  val get_atom : hcons_env -> Expr.t ->  atom

  val literal : atom -> Expr.t
  val weight : atom -> float
  val is_true : atom -> bool
  val neg : atom -> atom
  val vrai_atom  : atom
  val faux_atom  : atom
  val level : atom -> int
  val index : atom -> int
  val reason : atom -> reason
  val reason_atoms : atom -> atom list

  val dummy_var : var
  val dummy_atom : atom
  val dummy_clause : clause

  val to_float : int -> float
  val to_int : float -> int

  val fresh_name : unit -> string

  val fresh_lname : unit -> string

  val fresh_dname : unit -> string

  val make_clause : string -> atom list -> Expr.t -> int -> bool ->
    premise-> clause

  (*val made_vars_info : unit -> int * var list*)

  val cmp_atom : atom -> atom -> int
  val eq_atom   : atom -> atom -> bool
  val hash_atom  : atom -> int
  val tag_atom   : atom -> int

  val add_atom : hcons_env -> Expr.t -> var list -> atom * var list

  module Set : Set.S with type elt = atom
  module Map : Map.S with type key = atom
end

module Atom : ATOM

module type FLAT_FORMULA = sig
  type t
  type view = private UNIT of Atom.atom | AND of t list | OR of t list
  type hcons_env

  val equal   : t -> t -> bool
  val compare : t -> t -> int
  val print   : Format.formatter -> t -> unit
  val print_stats : Format.formatter -> unit
  val vrai    : t
  val faux    : t
  val view    : t -> view
  val mk_lit  : hcons_env -> Expr.t -> Atom.var list -> t * Atom.var list
  val mk_and  : hcons_env -> t list -> t
  val mk_or   : hcons_env -> t list -> t
  val mk_not  : t -> t
  val empty_hcons_env : unit -> hcons_env
  val nb_made_vars : hcons_env -> int
  val get_atom : hcons_env -> Expr.t -> Atom.atom

  val simplify :
    hcons_env ->
    Expr.t ->
    (Expr.t -> t * 'a) ->
    Atom.var list ->
    t * (Expr.t * (t * Atom.atom)) list
    * Atom.var list

  val get_proxy_of : t ->
    (Atom.atom * Atom.atom list * bool) Util.MI.t -> Atom.atom option

  val cnf_abstr :
    hcons_env ->
    t ->
    (Atom.atom * Atom.atom list * bool) Util.MI.t ->
    Atom.var list ->
    Atom.atom
    * (Atom.atom * Atom.atom list * bool) list
    * (Atom.atom * Atom.atom list * bool) Util.MI.t
    * Atom.var list

  val expand_proxy_defn :
    Atom.atom list list ->
    Atom.atom * Atom.atom list * bool -> Atom.atom list list

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

module Flat_Formula : FLAT_FORMULA

module Proxy_formula : sig
  val get_proxy_of : Expr.t ->
    Atom.atom Expr.Map.t -> Atom.atom option

  val mk_cnf :
    Atom.hcons_env ->
    Expr.t ->
    Atom.atom Expr.Map.t * Expr.t Atom.Map.t *
    Atom.var list * Atom.atom list list ->
    Atom.atom *
    (Atom.atom Expr.Map.t * Expr.t Atom.Map.t *
     Atom.var list * Atom.atom list list)
end
