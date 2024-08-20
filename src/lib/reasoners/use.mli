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

module SA : Set.S with type elt = Expr.t * Explanation.t

type t
type r = Shostak.Combine.r

val src : Logs.src
val empty : t
val find : r -> t -> Expr.Set.t * SA.t
val add : r -> Expr.Set.t * SA.t -> t -> t
val mem : r -> t -> bool
val print : t -> unit
val up_add : t -> Expr.t -> r -> r list -> t
val congr_add : t -> r list -> Expr.Set.t
val up_close_up :t -> r -> r -> t
val congr_close_up : t -> r -> r list -> Expr.Set.t * SA.t
