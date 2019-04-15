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

(** A simplified formula/expr/... type.
    the diff field is set to false if the operation did not change the
    input.
*)
type ('expr, 'abs_val) simp
val get_expr : ('e,_) simp -> 'e
val get_abs_val : (_, 'v) simp -> 'v
val has_changed : _ simp -> bool

(** As the simplifyer interacts with different components of alt-ergo,
    it is written to be as generic as possible.
    The simplifyer is then a functor of different modules which type is
    defined below.
*)

module type Dom =
sig
  type v
  type expr

  (** Top/Bottom value *)
  val top : v
  val bottom : v

  (** (Partial) Compare function *)
  val compare : v -> v -> int option

  (** Join operator *)
  val join : v -> v -> v

  (** Add constraint *)
  val add_constraint : expr -> v -> v

  (** Constants *)
  val vrai : v
  val faux : v
end

(** Expr is the signature of the module dedicated to
    the representation of expressions that are to be
    simplified. *)
module type Expr = sig
  type t
  val equal : t -> t -> bool
  val mk_term : Symbols.t -> t list -> Ty.t -> t
  val get_comp : t -> Symbols.t
  val get_sub_expr : t -> t list
  val get_type : t -> Ty.t
  val neg : t -> t
  val vrai : t
  val faux : t
  val int : string -> t
  val real : string -> t
  val print : Format.formatter -> t -> unit
end

(** This is the signature of the simplifyer. *)
module type S =
sig
  type v
  type expr

  (** Simplifies an expression and returns its associated abstract value. *)
  val simp_expr : expr -> (expr, v) simp
end

module SimpleReasoner
    (E : Expr)
    (D : Dom with type expr = E.t)
  : S with type expr = E.t and type v = D.v
