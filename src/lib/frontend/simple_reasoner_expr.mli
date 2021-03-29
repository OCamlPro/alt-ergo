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

type 'abs_val add_constraint_res =
  | AlreadyTrue (* The constraint is already true *)
  | AlreadyFalse (* The constraint is already false*)
  | NewConstraint of 'abs_val (* The new abstract value *)

(** Dom is the signature of the abstact domain. *)
module type Dom = sig
  type v (* The raw abstract value. For the interval domain, an interval *)
  type state (* The global state representation. Usually a map of 'v's *)

  (** Top/Bottom value *)
  val top : state
  val bottom : state

  val _true : v
  val _false : v
  val unknown : v

  (** (Partial) Compare function *)
  val compare : state -> state -> int option

  (** Join operator *)
  val join : state -> state -> state
  val v_join : v -> v -> v

  (** Add constraint *)
  val add_constraint : Expr.t -> Expr.t -> Symbols.lit -> state -> state add_constraint_res

  (** If possible, adds `expr` to `state` with the value `v` *)
  val add_raw_value : Expr.t -> v -> state -> state

  (** Evaluates an expression in the given state. *)
  val eval_expr : Expr.t -> state -> v

  val pp : Format.formatter -> state -> unit
  val pp_v : Format.formatter -> v -> unit
end

(** This is the signature of the simplifyer. *)
module type S =
sig
  type v

  (** Empties the simplifier caches *)
  val empty_caches : unit -> unit

  (** Simplifies an expression and returns its associated abstract value. *)
  val simp_expr : Expr.t -> (Expr.t, v) simp
end

module SimpleReasoner
    (D : Dom)
  : S with type v = D.v
