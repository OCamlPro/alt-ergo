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

module Make (_ : Theory.S) : sig

  type t

  exception Bottom of Explanation.t * Expr.Set.t list * t

  val empty : unit -> t

  val is_true : t -> Expr.t -> (Explanation.t Lazy.t * int) option

  val assume : bool -> t -> (Expr.gformula * Explanation.t) list -> t

  val decide : t -> Expr.t -> int -> t

  (* forget decisions one by one *)
  val forget_decision : t -> Expr.t -> int -> t

  val reset_decisions : t -> t
  (*val solve : t -> t*)

  val get_decisions : t -> (int * Expr.t) list

end
