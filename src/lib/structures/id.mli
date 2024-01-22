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

type t = Hstring.t [@@deriving ord]

type typed = t * Ty.t list * Ty.t
(** Typed identifier of function. In order:
    - The identifier.
    - Types of its arguments.
    - The returned type. *)

val compare_typed : typed -> typed -> int
val equal : t -> t -> bool
val show : t -> string
val pp : t Fmt.t

module Namespace : sig
  module type S = sig
    val fresh : ?base:string -> unit -> string
  end

  module Internal : S
  module Skolem : S
  module Abstract : S

  val reinit : unit -> unit
  (** Resets the [fresh_internal_name], [fresh_skolem] and [fresh_abstract]
      counters. *)
end
