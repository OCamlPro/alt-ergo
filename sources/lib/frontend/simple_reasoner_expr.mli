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
type ('a,'expl) simp

val get_expr : ('a, _) simp -> 'a
val has_changed : _ simp -> bool
val get_expl : (_, 'expl) simp -> 'expl

(** As the simplifyer interacts with different components of alt-ergo,
    it is written to be as generic as possible.
    The simplifyer is then a functor of different modules which type is
    defined below.
*)

(** Expr is the signature of the module dedicated to
    the representation of expressions that are to be
    simplified. *)
module type Expr =
sig
  type t

  val equal : t -> t -> bool
  val mk_expr : Symbols.t -> t list -> Ty.t -> t

  (** Expressions are generally defined by 3 elements:
      - a type
      - a set of sub expressions
      - a composition operator *)
  val get_comp : t -> Symbols.t
  val get_sub_expr : t -> t list
  val get_type : t -> Ty.t

  val vrai : t
  val faux : t

  val real : string -> t
  val int : string -> t

  val pretty : Format.formatter -> t -> unit
end

(** Expl is the signature of the module dedicated to
    the explanations of the calculations. *)
module type Expl =
sig
  type t
  val empty : t
  val union : t -> t -> t
end

(** Th is the signature of the module dedicated to
    the interactions with the theory. *)
module type Th =
sig
  type expr
  type env
  type expl

  (** Empty environment. *)
  val empty : unit -> env

  (** Tries to decide the expression in argument given the environment.
      If it fails, returns None. Otherwise, provides the answer and
      an explanation (possibly empty)
  *)
  val bool_query : expr -> env -> (bool * expl) option

  (** Tries to decide the arithmetic value of an expression given the
      environment.
      If it fails, returns None. Otherwise, provides the answer and
      an explanation (possibly empty) *)
  val q_query :  expr -> env -> (Q.t * expl) option
end

(** This is the signature of the simplifyer. *)
module type S =
sig
  (** The type of expressions. *)
  type expr

  (** The type of environments the theory works in. *)
  type env

  (** The type of explanations *)
  type expl

  (** Sets the environment to be used in the simplifyer.
      Set to empty by default. *)
  val set_env : env -> unit

  (** Simplifies an expression. *)
  val simp_expr : expr -> (expr,expl) simp
end

module SimpleReasoner
    (E : Expr)
    (Expl : Expl)
    (T : Th with type expr = E.t and type expl = Expl.t)
  : S with type expr = E.t and type env = T.env and type expl = Expl.t
