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

(* TODO: update the documentation. *)
(** Maps of values for alt-ergo's models.
    Elements are sorted by symbols/types (P) and accumulated as sets
    of expressions matching the P.key type (V).
*)

type sig_ = string * Ty.t list * Ty.t
(** Signature of a model value. *)

module Value : sig
  type abs_or_const = [
    | `Abstract of sig_
    | `Constant of Shostak.Combine.r * string
  ]

  type array = [
    | `Abstract of sig_
    | `Store of array * abs_or_const * abs_or_const
  ]

  type t = [
    | `Array of array
    | `Constructor of string * (abs_or_const list)
    | abs_or_const
  ]

  val pp : t Fmt.t
end

type t

val add : sig_ -> Value.t list -> Value.t -> t -> t
val create : sig_ list -> t
val pp : t Fmt.t
