(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2020-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

(** {1 Models module} *)

module Sorts : Map.S with type key = string

module Profile : sig

  module P : Map.S with type key =
                          Symbols.t * Ty.t list * Ty.t
  module V : Set.S with type elt =
                          (Expr.t * (Shostak.Combine.r * string)) list *
                          (Shostak.Combine.r * string)

  val add : P.key -> V.elt -> V.t P.t -> V.t P.t
  val iter : (P.key -> 'a -> unit) -> 'a P.t -> unit
  val fold : (P.key -> 'a -> 'b -> 'b) -> 'a P.t -> 'b -> 'b
  val empty : 'a P.t
  val is_empty : 'a P.t -> bool
end

(** Print the given counterexample on the given formatter with the
    corresponding format setted with Options.get_output_format *)
val output_concrete_model :
  Format.formatter ->
  Expr.Set.t ->
  Profile.V.t Profile.P.t ->
  Profile.V.t Profile.P.t ->
  Profile.V.t Profile.P.t ->
  unit
