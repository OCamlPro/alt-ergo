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

type 'a ac =
  {h: Symbols.t ; t: Ty.t ; l: ('a * int) list; distribute: bool}

type abs_kind =
    Ac (** Semantic value abstracted for AC(X) purposes. *)
(** Type of abstractions that can be used in [abstract]. Used to distinguish
    the reason for which a semantic value was abstracted, which some code
    cares about (see {!module-Arith}). *)

type 'a solve_pb = { sbt : ('a * 'a) list; eqs : ('a * 'a) list }

module type SHOSTAK = sig

  (**Type of terms of the theory*)
  type t

  (**Type of representants of terms of the theory*)
  type r

  (** Name of the theory*)
  val name : string

  val timer : Timers.ty_module

  val is_mine_symb : Symbols.t -> bool
  (** Return [true] if the symbol is owned by the theory. *)

  (** Give a representant of a term of the theory*)
  val make : Expr.t -> r * Expr.t list

  val term_extract : r -> Expr.t option * bool (* original term ? *)

  val color : (r ac) -> r

  val type_info : t -> Ty.t

  val embed : r -> t
  val is_mine : t -> r

  (** Give the leaves of a term of the theory *)
  val leaves : t -> r list

  (** Determines whether the semantic value is a constant value. [is_constant t]
      is equivalent to [leaves t == []] (except for the special cases below),
      but is more efficient.

      In addition, some terms (e.g. [true], [false], [void]) that have no
      associated theories are considered as constant by this function.

      Semantic value for which [is_constant] returns [true] contains no free
      names and thus have the same concrete value in all contexts.

      Note that for some theories (e.g. records, arrays) the constant may not be
      pure: it may involve nested (constant) terms of other theories. *)
  val is_constant : t -> bool

  val subst : r -> r -> t -> r

  val compare : r -> r -> int

  (* tests if two values are equal (using tags) *)
  val equal : t -> t -> bool

  val hash : t -> int
  (** solve r1 r2, solve the equality r1=r2 and return the substitution *)

  val solve : r -> r ->  r solve_pb -> r solve_pb

  val print : Format.formatter -> t -> unit

  (** return true if the symbol is fully interpreted by the theory, i.e. it
      is fully embedded into semantic values and does not need term-level
      congruence *)
  val fully_interpreted : Symbols.t -> bool

  val abstract_selectors : t -> (r * r) list -> r * (r * r) list

  val assign_value :
    r -> r list -> (Expr.t * r) list -> (Expr.t * bool) option
  (**[assign_value r distincts eq] selects the value to assign to [r] in the
     model as a term [t], and returns [Some (t, is_cs)]. [is_cs] is described
     below.

     If no appropriate value can be chosen here, return [None] (only do this if
     either [r] is already a value, or there is a mechanism somewhere else in
     the code, such as the [case_split] function of a relation module, that
     ensures completeness of the generated model).

     [r] is the current class representative that a value should be chosen for.
     No assumptions should be made on the shape of [r], but do return [None] if
     it is already a value.

     [distincts] is a list of term representatives that the returned value must
     be distinct from (choosing a value that is present in [distincts] will
     cause the solver to loop infinitely).

     [eq] is a list of pairs [(t, r)] of terms and their initial representative
     (i.e., [r] is [fst (X.make t)] for each pair) that encode the equivalence
     class of [r].

     The returned bool serves a similar purpose as the [is_cs] flag in
     [Th_util.case_split].

     It should usually be [true], which indicates that the returned term is not
     forced.

     Use [false] only when the returned term contains aliens that should be
     assigned (e.g. records).

     **When returning [false], you must ensure that the equality between the
     first argument and the return value always hold (i.e. is a *unit* fact).
     In particular, the equality *must not* depend on [distincts] -- doing so
     would be unsound.**

     In other words, if [assign_value r distincts eq] returns
     [Some (t, false)], then there must be no context in which
     [solve r (fst X.make t)] raises [Unsolvable]. You have been warned! *)

  val to_model_term : r -> Expr.t option
  (** [to_model_term r] creates a model term if [r] is constant.
      The function cannot fail if [r] is a constant (that is statisfied the
      predicate [X.is_constant]).

      The returned value always satisfies the predicate
      [Expr.is_model_term]. See its documentation for more details about
      model terms. *)
end

module type X = sig
  type r

  val save_cache : unit -> unit
  (** saves the module's current cache *)

  val reinit_cache : unit -> unit
  (** restores the module's cache *)

  val make : Expr.t -> r * Expr.t list

  val type_info : r -> Ty.t

  val str_cmp : r -> r -> int

  val hash_cmp : r -> r -> int

  val equal : r -> r -> bool

  val hash : r -> int

  val leaves : r -> r list

  val is_constant : r -> bool

  val subst : r -> r -> r -> r

  val solve : r -> r ->  (r * r) list

  val term_embed : Expr.t -> r

  val term_extract : r -> Expr.t option * bool (* original term ? *)

  val ac_embed : r ac -> r

  val ac_extract : r -> (r ac) option

  val abstract : kind:abs_kind -> r -> r
  (** [abstract ~kind r] returns an abstracted constant representing [r].

      The abstract constant [abstract ~kind r] is {e definitionally equal} to
      [r]: when processed by the {!module-Uf} and {!module-Ccx} modules in any
      context, the equality [r = abstract ~kind r] is introduced automatically.

      Calling [abstract ~kind r] multiple times with the same [kind] and the
      same [r] always returns the same abstracted constant.

      Abstracted constants, like terms, are terminal leaves: the only leaf of
      [abstract ~kind r] is [abstract ~kind r] itself. In particular,
      substituting the leaves of [r] does not impact [abstract ~kind r].
  *)

  val is_abstract : ?kind:abs_kind -> r -> bool
  (** [is_abstract ?kind r] returns [true] if [r] is an abstracted constant
      created with {!val-abstract} with the provided [kind] (if any).
  *)

  val abstract_extract : r -> r option
  (** [abstract_extract r] returns the inner abstracted semantic value
      embedded in [r], if any.

      If [abstract_extract r] is [Some r'], then [r] is definitionally equal to
      [r'], that is, the equation [r = r'] holds in all contexts.

      {b Note}: While [abstract_extract (abstract ~kind r)] and [r] are
      guaranteed to be definitionally equal, they are not, in general,
      guaranteed to be equal as semantic values according to {!val-equal}.
  *)

  val color : (r ac) -> r

  val fully_interpreted : Symbols.t -> bool

  val is_a_leaf : r -> bool

  val print : Format.formatter -> r -> unit

  val abstract_selectors : r -> (r * r) list -> r * (r * r) list

  val is_solvable_theory_symbol : Symbols.t -> bool

  (* the returned bool is true when the returned term in a constant of the
     theory. Otherwise, the term contains aliens that should be assigned
     (eg. records). In this case, it's a unit fact, not a decision
  *)
  val assign_value :
    r -> r list -> (Expr.t * r) list -> (Expr.t * bool) option

  val to_model_term : r -> Expr.t option
  (** [to_model_term r] creates a model term if [r] is constant.
      The function cannot fail if [r] is a constant (that is statisfied the
      predicate [X.is_constant]).

      The returned value always satisfies the predicate
      [Expr.is_model_term]. See its documentation for more details about
      model terms. *)
end
