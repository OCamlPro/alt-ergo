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

module Make (Th : Theory.S) : sig

  type t

  exception Bottom of Explanation.t * Term.Set.t list * t

  val empty : unit -> t

  val is_true : t -> Formula.t -> (Explanation.t Lazy.t * int) option

  val assume : bool -> t -> (Formula.gformula * Explanation.t) list -> t

  val decide : t -> Formula.t -> int -> t

  (* forget decisions one by one *)
  val forget_decision : t -> Formula.t -> int -> t

  val reset_decisions : t -> t
  (*val solve : t -> t*)

  val get_decisions : t -> (int * Formula.t) list

end
