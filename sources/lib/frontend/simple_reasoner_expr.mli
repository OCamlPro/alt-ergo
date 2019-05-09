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
type 'a simp

val get_expr : 'a simp -> 'a
val has_changed : 'a simp -> bool

module type Th =
sig
  type expr
  type env
  val empty : unit -> env
  val query : expr -> env -> bool end

module type S =
sig
  type expr
  type env

  val set_env : env -> unit

  (** Simplifies an expression *)
  val simp_expr : expr -> expr simp
end

module SimpleReasoner
    (E :
     sig
       (** Expressions are generally defined by 3 elements:
           - a type
           - a set of sub expressions
           - a composition operator *)
       type t
       val equal : t -> t -> bool
       val mk_expr : Symbols.t -> t list -> Ty.t -> t

       val get_comp : t -> Symbols.t
       val get_sub_expr : t -> t list
       val get_type : t -> Ty.t

       val vrai : t
       val faux : t

       val real : string -> t
       val int : string -> t
       val neg : t -> t option

       val pretty : Format.formatter -> t -> unit

     end)
    (T : Th with type expr = E.t) : S with type expr = E.t and type env = T.env
