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

type sy = Id.t * Ty.t list * Ty.t
(** Typed symbol of function. *)

module Value : sig
  type simple =
    | Abstract of sy
    (** An unique abstract value. *)

    | Constant of string
    (** A string representation of a semantic value. *)

  type record = string * simple list

  type array =
    | AbstractArray of sy
    (** An unique abstract array value. *)

    | Store of array * simple * simple
    (** An array store: [(store array key value)]. *)

  type t =
    | Array of array

    | Record of record
    (** A string representation of a record definition. *)

    | Simple of simple

  val pp : t Fmt.t
  (** [pp ppf v] prints the model value [v] on the formatter [ppf] using the
      SMT-LIB format. *)
end

type t
(** Type of model. *)

val add : sy -> Value.t list -> Value.t -> t -> t
(** [add sy args ret mdl] adds the binding [args -> ret] to the partial graph
    associated with the symbol [sy]. *)

val empty : suspicious:bool -> t
(** An empty model. The [suspicious] flag is used to remember that this
    model may be wrong as it involves symbols from theories for which the
    model generation is known to be incomplete. *)

val pp : t Fmt.t
(** [pp ppf mdl] prints the model [mdl] on the formatter [ppf] using the
    SMT-LIB format. *)
