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

type sig_ = Id.t * Ty.t list * Ty.t
(** Signature of a model value. *)

module Value : sig
  type array = [
    | `Abstract of sig_
    (** An unique abstract array value. *)

    | `Store of array * string * string
    (** An array store: [(store array key value)]. *)
  ]

  type t = [
    | `Abstract of sig_
    (** An unique abstract value. *)

    | `Constant of string
    (** A string representation of a semantic value. *)

    | `Array of array

    | `Constructor of string * (string list)
    (** A string representation of a constructor application. *)
  ]

  val pp : t Fmt.t
  (** [pp ppf v] prints the model value [v] on the formatter [ppf] using the
      SMT-LIB format. *)
end

type t

val add : sig_ -> Value.t list -> Value.t -> t -> t

val create : sig_ list -> t

val pp : t Fmt.t
(** [pp ppf mdl] prints the model [mdl] on the formatter [ppf] using the
    SMT-LIB format. *)
