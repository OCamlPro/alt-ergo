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
  val simp_expr : expr -> expr
end

module SimpleReasoner
    (E :
     sig
       (** Expressions are generally defined by 3 elements:
           - a type
           - a set of sub expressions
           - a composition operator *)
       type expr

       val mk_expr : Symbols.t -> expr list -> Ty.t -> expr

       val get_comp : expr -> Symbols.t
       val get_sub_expr : expr -> expr list
       val get_type : expr -> Ty.t

       val vrai : expr
       val faux : expr

       val real : string -> expr
       val int : string -> expr
       val equal : expr -> expr -> bool

       val pretty : Format.formatter -> expr -> unit

     end) : S with type expr = E.expr
