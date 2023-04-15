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

(** Maps of values for alt-ergo's models.
    Elements are sorted by symbols/types (P) and accumulated as sets
    of expressions matching the P.key type (V).
*)

module P : Map.S with type key =
                        Symbols.t * Ty.t list * Ty.t

module V : Set.S with type elt =
                        (Expr.t * (Types.r * string)) list *
                        (Types.r * string)

type key = P.key
type elt = V.t
type t = V.t P.t

val add : key -> V.elt -> t -> t

val iter : (key -> elt -> unit) -> t -> unit

val fold : (key -> elt -> 'acc -> 'acc) -> t -> 'acc -> 'acc

val empty : t

val is_empty : t -> bool
