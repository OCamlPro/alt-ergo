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
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

type t

type r = Shostak.Combine.r

module LX : Xliteral.S with type elt = r

val empty : unit -> t
val add : t -> Expr.t -> t * Expr.t list

val mem : t -> Expr.t -> bool

val find : t -> Expr.t -> r * Explanation.t

val find_r : t -> r -> r * Explanation.t

val union :
  t -> r -> r -> Explanation.t ->
  t * (r * (r * r * Explanation.t) list * r) list

val distinct : t -> r list -> Explanation.t -> t

val are_equal : t -> Expr.t -> Expr.t -> added_terms:bool -> Th_util.answer
val are_distinct : t -> Expr.t -> Expr.t -> Th_util.answer
val already_distinct : t -> r list -> bool

val class_of : t -> Expr.t -> Expr.t list
val rclass_of : t -> r -> Expr.Set.t

val cl_extract : t -> Expr.Set.t list
val model : t ->
  (r * Expr.t list * (Expr.t * r) list) list * (Expr.t list) list

val print : Format.formatter -> t -> unit
val term_repr : t -> Expr.t -> Expr.t

val make : t -> Expr.t -> r (* may raise Not_found *)

val is_normalized : t -> r -> bool

val assign_next : t -> (r Xliteral.view * bool * Th_util.lit_origin) list * t
val output_concrete_model : t -> unit
