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

open Types

module Combine : Sig.X

module Polynome : (module type of Polynome)
module Arith : Sig.SHOSTAK with type t = polynome

module Records : Sig.SHOSTAK with type t = Types.records

module Bitv : Sig.SHOSTAK with type t = Types.bitv

module Arrays : Sig.SHOSTAK with type t = Types.arrays

module Enum : Sig.SHOSTAK with type t = Types.enum

module Adt : Sig.SHOSTAK with type t = Types.adt

module Ite : Sig.SHOSTAK with type t = Types.ite

module Ac : (module type of Ac)

(** map of semantic values using Combine.hash_cmp *)
module MXH : Map.S with type key = Types.r

(** set of semantic values using Combine.hash_cmp *)
module SXH : Set.S with type elt = Types.r

(** map of semantic values using structural compare Combine.str_cmp *)
module MXS : Map.S with type key = Types.r

(** set of semantic values using structural compare Combine.str_cmp *)
module SXS : Set.S with type elt = Types.r

val init : unit -> unit
