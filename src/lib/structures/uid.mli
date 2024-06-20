(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
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

module DE = Dolmen.Std.Expr

type t = private
  | Hstring : Hstring.t -> t
  | Dolmen : 'a DE.id -> t
  | Term_cst : DE.term_cst -> t
  | Ty_cst : DE.ty_cst -> t

type hash = {
  to_int : t -> int;
  (** Return a hash for the constructor. This hash is between [0] and [n]
      exclusive where [n] is the number of constructors of the ADT. *)

  of_int : int -> t;
  (** Return the associated constructor to the integer.

      @raises Invalid_argument if the integer does not correspond to
       a constructor of this ADT. *)
}
(** Minimal perfect hash function for the constructors of an ADT. *)

val of_dolmen : 'a DE.Id.t -> t
val of_term_cst : DE.term_cst -> t
val of_ty_cst : DE.ty_cst -> t
val of_string : string -> t
val of_hstring : Hstring.t -> t

val to_term_cst : t -> DE.term_cst

val hash : t -> int
val pp : t Fmt.t
val show : t -> string
val equal : t -> t -> bool
val compare : t -> t -> int

val hash_tag : hash DE.Tags.t
val set_hash : t -> hash -> unit
val get_hash : t -> hash

module Set : Set.S with type elt = t
module Map : Map.S with type key = t
