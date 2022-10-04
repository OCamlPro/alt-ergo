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

type builtin = Symbols.builtin =
    LE | LT | (* arithmetic *)
    IsConstr of Hstring.t (* ADT tester *)

type 'a view = (*private*)
  | Eq of 'a * 'a
  | Distinct of bool * 'a list
  | Builtin of bool * builtin * 'a list
  | Pred of 'a * bool

type 'a atom_view
(* We do not need to export internal representation
   of literals !
   =
   | EQ of 'a * 'a
   | BT of builtin * 'a list
   | PR of 'a
   | EQ_LIST of 'a list*)

module type OrderedType = sig
  type t
  val compare : t -> t -> int
  val hash :  t -> int
  val print : Format.formatter -> t -> unit
  val top : unit -> t
  val bot : unit -> t
  val type_info : t -> Ty.t
end

module type S = sig
  type elt
  type t

  val make : elt view -> t
  val view : t -> elt view
  val atom_view : t -> elt atom_view * bool (* is_negated ? *)

  val mk_eq : elt -> elt -> t
  val mk_distinct : bool -> elt list -> t
  val mk_builtin : bool -> builtin -> elt list -> t
  val mk_pred : elt -> bool -> t

  val mkv_eq : elt -> elt -> elt view
  val mkv_distinct : bool -> elt list -> elt view
  val mkv_builtin : bool -> builtin -> elt list -> elt view
  val mkv_pred : elt -> bool -> elt view

  val neg : t -> t

  val add_label : Hstring.t -> t -> unit
  val label : t -> Hstring.t

  val print : Format.formatter -> t -> unit

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val uid : t -> int
  val elements : t -> elt list

  val save_cache : unit -> unit
  (** Saves the modules cache  *)

  val reinit_cnt: unit -> unit
  (** Reinitializes the module's cache *)

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t
end

val print_view :
  ?lbl:string ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter ->
  'a view ->
  unit

module Make ( X : OrderedType ) : S with type elt = X.t
