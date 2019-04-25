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

module type S =
sig
  type expr

  (** Adds/replaces the value of an expression. This expression will be replaced by a
      constant if possible *)
  val bind_expr_val : expr -> Num.num -> unit

  (** Adds/replaces the value of an expression. This expression will be replaced by a
      constant if possible *)
  val bind_expr_bool : expr -> bool -> unit

  (** Simplifies an expression *)
  val simp_expr : expr -> expr
end

module SimpleReasoner
    (E :
     sig
       (** Expressions are generally defined by 3 elements:
           - a type
           - a set of sub expressions
           - a composition operator *)
       type t
       val hash : t -> int
       val equal : t -> t -> bool
       val mk_expr : Symbols.t -> t list -> Ty.t -> t

       val get_comp : t -> Symbols.t
       val get_sub_expr : t -> t list
       val get_type : t -> Ty.t

       val vrai : t
       val faux : t

       val real : string -> t
       val int : string -> t

       val pretty : Format.formatter -> t -> unit

     end) : S with type expr = E.t
