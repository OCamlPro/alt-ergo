(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

module type S = sig
  type t
  type r

  val empty : unit -> t
  val add : t -> Term.t -> t * Literal.LT.t list

  val mem : t -> Term.t -> bool

  val find : t -> Term.t -> r * Explanation.t

  val find_r : t -> r -> r * Explanation.t

  val union :
    t -> r -> r -> Explanation.t ->
    t * (r * (r * r * Explanation.t) list * r) list

  val distinct : t -> r list -> Explanation.t -> t

  val are_equal : t -> Term.t -> Term.t -> added_terms:bool -> Sig.answer
  val are_distinct : t -> Term.t -> Term.t -> Sig.answer
  val already_distinct : t -> r list -> bool

  val class_of : t -> Term.t -> Term.t list
  val rclass_of : t -> r -> Term.Set.t

  val cl_extract : t -> Term.Set.t list
  val model : t ->
    (r * Term.t list * (Term.t * r) list) list * (Term.t list) list

  val print : Format.formatter -> t -> unit
  val term_repr : t -> Term.t -> Term.t

  val make : t -> Term.t -> r (* may raise Not_found *)

  val is_normalized : t -> r -> bool

  val assign_next : t -> (r Literal.view * bool * Sig.lit_origin) list * t
  val output_concrete_model : t -> unit
end

module Make (X : Sig.X) : S with type r = X.r
