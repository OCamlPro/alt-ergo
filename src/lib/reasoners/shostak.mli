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

module Combine : sig
  include Sig.X

  val src : Logs.src

  val top : r
  val bot : r
end

module Polynome : Polynome.T
  with type r = Combine.r

module Arith : Sig.SHOSTAK
  with type r = Combine.r and type t = Polynome.t

module Records : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Records.abstract

module Bitv : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Bitv.abstract

module Adt : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Adt.abstract

module Ac : Ac.S with type r = Combine.r and type t = Combine.r Sig.ac

(** map of semantic values using Combine.hash_cmp *)
module MXH : Map.S with type key = Combine.r

(** set of semantic values using Combine.hash_cmp *)
module SXH : Set.S with type elt = Combine.r

module L : Xliteral.S with type elt = Combine.r

module Literal : Literal.S with type elt = L.t

module HX : Hashtbl.S with type key = Combine.r
