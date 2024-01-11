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


module type ATOM = sig

  type var =
    {  vid : int;
       pa : atom;
       (* Pointer to the positive atom having this variable as
          underlying variable. *)

       na : atom;
       (* Pointer to the nagative atom having this variable as
          underlying variable. *)

       mutable weight : float;
       mutable seen : bool;
       mutable level : int;
       (** Decision level. For more details, see the documention of the field
           [trail] of the environment of SatML. *)

       mutable index : int;
       (** Position in the trail, debug only.

           This position doesn't correspond to a propagation level,
           see the documention of the field [trail] of the environment of
           SatML. *)

       mutable hindex : int;
       (** Index in heap. *)

       mutable reason: reason;
       (** If the value is [Some c], the clause [c] is the reason for
           which [pa] or [na] have been assigned to be [true]. *)

       mutable vpremise : premise}

  and atom = {
    var : var;
    (** The underlying variable. *)

    lit : Expr.t;
    (** The underlying literal. *)

    neg : atom;
    (** The negation of this atom. *)

    mutable watched : clause Vec.t;
    (** List of clauses watched by this atom. *)

    mutable is_true : bool;
    (** Determine if the atom is assigned. An atom [a] and its
        negation [a.neg] cannot be both assigned. *)

    mutable timp : int;
    mutable is_guard : bool;
    (** Determine if the atom is used as an incremental guard. *)

    aid : int
  }

  and clause = {
    name : string;
    mutable atoms : atom Vec.t;
    (** Atoms of the clause.

        A clause has always at least two atoms and
        the negations of the two first atoms watch the clause. *)

    mutable activity : float;
    mutable removed : bool;
    (** If this flag is set to [true], the clause is ignored during
        the boolean constraint propagation. More precisely, if the clause
        is watched by an atom [a], we don't propagate constraints in this
        clause after assigned [a] to [true].

        Satisfied clauses (that is clauses whose one of their atoms has been
        decided at the level [0]) can be removed for sake of performance. *)

    learnt : bool;
    (** This flag is set to [true] if the clause have been learnt by solver. *)

    cpremise : premise;
    form : Expr.t
  }

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

  val cmp_var : var -> var -> int

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
  (* Type of hconsed flat formula. *)

  type view = private
    | UNIT of Atom.atom
    (** [UNIT a] represents an atom. *)

    | AND of t list
    (** [AND (A1, ..., An)] represents the n-ary [AND] gate
         A1 /\ ... /\ An
        with the following invariants:
        - There are at least two elements;
        - No duplicate;
        - None of the [Ai] are [AND] gates;
        - The elements are in increasing order for the function [compare];
        - The gate doesn't contain a contradiction. *)

    | OR of t list
    (** [OR (A1, ..., An)]) represents the n-ary [OR] gate
         A1 \/ ... \/ An
        with the following invariants:
        - There are at least two elements;
        - No duplicate;
        - None of the [Ai] are [OR] gates;
        - The elements are in increasing order for the function [compare];
        - The gate doesn't contain tautology. *)

  type hcons_env
  (* Environment of the hconsing. *)

  val equal   : t -> t -> bool
  (** [equal f1 f2] checks the equality of the hashes of [f1] and [f2]. *)

  val compare : t -> t -> int
  (** [compare f1 f2] compares the two flat formulas [f1] and [f2] using hashes.

      By construction, the negation of a flat formula [f] is the immediate
      successor or predecessor of [f] for this comparison function.

      [vrai] is the smallest element for this order and [faux] is
      the second smallest element. *)

  val print   : Format.formatter -> t -> unit
  val vrai    : t
  val faux    : t
  val view    : t -> view
  val mk_lit  : hcons_env -> Expr.t -> Atom.var list -> t * Atom.var list
  val mk_and  : hcons_env -> t list -> t
  (** [mk_and l] where [l = [f1; ...; fn]] is a flat formula equivalent to
      [f1 /\ ... /\ fn]. *)

  val mk_or   : hcons_env -> t list -> t
  (** [mk_or l] where [l = [f1; ...; fn]] is a flat formula equivalent to
      [f1 \/ ... \/ fn]. *)

  val mk_not  : t -> t
  (** [mk_not f] is a flat formula equivalent to the negation of [f]. *)

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
  (** [simplify henv f abstr acc] creates a flat formula from the
      expression formula [f] in the hconsing environment [henv].

      The [abstr] function is used to hit a cache of abstract atoms used to
      represent lemmas.

      @return [(ff, new_abstrs, new_vars)] where
      - [ff] is the flat formula built from [f].
      - [new_abstrs] is the list of abstractions created for lemmas in [f].
           The internal cache of [abstr] has to be updated with the new
           abstractions before recalling [simplify].
      - [new_vars] is an accumulator of all the new atoms. *)

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
