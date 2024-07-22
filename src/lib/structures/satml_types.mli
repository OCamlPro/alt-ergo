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

module type ATOM = sig

  type var =
    {  vid : int;
       pa : atom;
       na : atom;
       mutable weight : float;
       mutable seen : bool;
       mutable level : int; (* decision level *)
       mutable index : int; (* position in the trail, debug only *)
       mutable hindex : int; (* index in heap *)
       mutable reason: reason;
       mutable vpremise : premise}

  and atom =
    { var : var;
      lit : Shostak.Literal.t;
      neg : atom;
      mutable watched : clause Vec.t;
      mutable is_true : bool;
      mutable timp : int;
      mutable is_guard : bool;
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

  val literal : atom -> Shostak.Literal.t
  val weight : atom -> float
  val is_true : atom -> bool
  val neg : atom -> atom
  val vrai_atom  : atom
  val faux_atom  : atom
  val level : atom -> int
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

  val make_clause : string -> atom list -> Expr.t -> bool ->
    premise-> clause

  (*val made_vars_info : unit -> int * var list*)

  val equal_var : var -> var -> bool
  val compare_var : var -> var -> int
  val hash_var : var -> int

  val cmp_atom : atom -> atom -> int
  val eq_atom   : atom -> atom -> bool
  val hash_atom  : atom -> int
  val tag_atom   : atom -> int

  val add_atom :
    hcons_env -> Shostak.Literal.t -> var list -> atom * var list
  val add_expr_atom : hcons_env -> Expr.t -> var list -> atom * var list

  module Set : Set.S with type elt = atom
  module Map : Map.S with type key = atom
end

module Atom : ATOM

module type FLAT_FORMULA = sig
  type t
  type view = private UNIT of Atom.atom | AND of t list | OR of t list
  type hcons_env

  type proxy_defn
  (** A proxy definition, encoding an equivalence [p <=> l_1 /\ ... /\ l_n] or
      [p <=> l_1 \/ ... \/ l_n] where [p] is a proxy and [l_1], ..., [l_n] are
      literals.

      See [get_proxy_of] and [expand_proxy_defn]. *)

  type proxies
  (** Mapping from flat formulas to their proxy definition, if any. *)

  val empty_proxies : proxies

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
  val atom_hcons_env : hcons_env -> Atom.hcons_env

  val simplify :
    hcons_env ->
    Expr.t ->
    (Expr.t -> t * 'a) ->
    Atom.var list ->
    t * (Expr.t * (t * Atom.atom)) list
    * Atom.var list

  val get_proxy_of : t -> proxies -> Atom.atom option
  (** [get_proxy_of ff proxies] returns the proxy registered for [ff] in
      [proxies], if it exists.

      Note: If [ff] is a unit formula (i.e. a literal), [get_proxy_of] returns
      [None].

      The proxy of a flat formula [ff] is an atom [p] with the (implicit)
      equivalent [p <=> ff]. Proxies are used to perform lazy CNF conversion of
      formulas in the CDCL-Tableaux solver. *)

  val cnf_abstr :
    hcons_env ->
    t ->
    proxies ->
    Atom.var list ->
    Atom.atom
    * proxy_defn list
    * proxies
    * Atom.var list

  val expand_proxy_defn :
    Atom.atom list list -> proxy_defn -> Atom.atom list list
  (** Expand a proxy definition into clausal normal form.

      The definition [p <=> l_1 \/ ... \/ l_n] is expanded into:

        [(~p \/ l_1 \/ ... \/ l_n) /\ (p \/ ~l_1) /\ ... /\ (p \/ ~l_n)]

      and the definition [p <=> l_1 /\ ... /\ l_n] is expanded into:

        [(p \/ ~l_1 \/ ... \/ ~l_n) /\ (~p \/ l_1) /\ ... /\ (~p \/ l_n)] *)

  val reinit_cpt : unit -> unit
  (** Resets to 0 the counter *)

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
