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

module DE = Dolmen.Std.Expr

type _ t = private
  | Hstring : Hstring.t -> 'a t
  | Term_cst : DE.term_cst -> DE.term_cst t
  | Ty_cst : DE.ty_cst -> DE.ty_cst t
  | Ty_var : DE.ty_var -> DE.ty_var t

type term_cst = DE.term_cst t
type ty_cst = DE.ty_cst t
type ty_var = DE.ty_var t

val of_term_cst : DE.term_cst -> term_cst
val of_ty_cst : DE.ty_cst -> ty_cst
val of_ty_var : DE.ty_var -> ty_var
val of_string : string -> 'a t
val of_hstring : Hstring.t -> 'a t

val hash : 'a t -> int
val pp : 'a t Fmt.t
val show : 'a t -> string
val equal : 'a t -> 'a t -> bool
val compare : 'a t -> 'a t -> int

val do_mangle : (string -> string option) -> term_cst -> term_cst

val order_tag : int Dolmen.Std.Tag.t
(** Tag used to attach the order of constructor. *)

module Term_set : Set.S with type elt = term_cst
module Term_map : Map.S with type key = term_cst
module Ty_map : Map.S with type key = ty_cst
