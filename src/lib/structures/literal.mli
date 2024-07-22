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

(** This module contains a definition of a "combined" literal type that can
    contain both syntaxic literals (expressions) and semantic literals (that
    contain semantic values, see also the {!Xliteral} module). *)

type 'a view = LTerm of Expr.t | LSem of 'a
(** View over literals, parameterized by the type of semantic literals. Used for
    both pattern-matching and creation of literals (through the [make] and
    [view] functions). *)

val pp_view : 'a Fmt.t -> 'a view Fmt.t
(** Pretty-printer for views. *)

val hash_view : ('a -> int) -> 'a view -> int
(** Hash function for views. *)

val equal_view : ('a -> 'a -> bool) -> 'a view -> 'a view -> bool
(** Equality function for views. *)

val compare_view : ('a -> 'a -> int) -> 'a view -> 'a view -> int
(** Comparison function for views. *)

module type S = sig
  type elt
  (** The type of semantic elements literals. *)

  type t
  (** The type of syntaxic or semantic literals. *)

  val make : elt view -> t
  (** Create a new literal given its view. *)

  val view : t -> elt view
  (** Extract a view from a literal (for pattern-matching). *)

  val pp : t Fmt.t
  (** Pretty-printer for literals. *)

  val hash : t -> int
  (** Hash function for literals. *)

  val equal : t -> t -> bool
  (** Equality of literals. Note that this does not try to look into the
      semantic content of syntaxic literals: [x = y] as a term and [x = y] as a
      semantic literal (where [x] and [y] are semantic values) are distinct. *)

  val compare : t -> t -> int
  (** Comparison function over literals. The order is unspecified. *)

  val neg : t -> t
  (** [neg t] is the boolean negation of [t]. *)

  val normal_form : t -> t * bool
  (** [normal_form l] returns the normal form of [l]. The normal form of [l] is
      a pair [l', is_neg] such that:

      - [l'] is [neg l] if [is_neg] is [true]
      - [l'] is [l] if [is_neg] is [false]
      - [normal_form l'] is [l', false] *)
  val is_ground : t -> bool
  (** [is_ground l] is always [true] if [l] is a semantic literal, and otherwise
      is [true] iff the syntaxic literal is ground (does not contain free
      variables nor free type variables). *)

  module Table : Hashtbl.S with type key = t
  (** Hash tables over literals. *)

  module Set : Set.S with type elt = t
  (** Sets of literals. *)

  module Map : Map.S with type key = t
  (** Maps over literals. *)
end

module Make(Sem : Xliteral.S) : S with type elt = Sem.t
