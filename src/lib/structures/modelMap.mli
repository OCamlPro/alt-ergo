(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(** Maps of values for alt-ergo's models.
    Elements are sorted by symbols/types (P) and accumulated as sets
    of expressions matching the P.key type (V).
*)

module P : Map.S with type key =
                        Symbols.t * Ty.t list * Ty.t

module V : Set.S with type elt =
                        (Expr.t * (Shostak.Combine.r * string)) list *
                        (Shostak.Combine.r * string)

type key = P.key
type elt = V.t

type t

val add : key -> V.elt -> t -> t

val iter : (key -> elt -> unit) -> t -> unit

val fold : (key -> elt -> 'acc -> 'acc) -> t -> 'acc -> 'acc

val empty : t

val is_empty : t -> bool

val is_suspicious : t -> bool
(* Determine if the model is suspicious as it contains symbols
   of theories for which the model generation is not properly supported. *)
