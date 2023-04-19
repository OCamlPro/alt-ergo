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

type 'a t = { mutable dummy: 'a; mutable data : 'a array; mutable sz : int }
val make : int -> 'a -> 'a t
val init : int -> (int -> 'a) -> 'a -> 'a t
val from_array : 'a array -> int -> 'a -> 'a t
val from_list : 'a list -> int -> 'a -> 'a t
val clear : 'a t -> unit

(* if bool is true, then put "dummy" is unreachable cells *)
val shrink : 'a t -> int -> bool -> unit
val pop : 'a t -> unit
val size : 'a t -> int
val is_empty : 'a t -> bool
val grow_to : 'a t -> int -> unit
val grow_to_double_size : 'a t -> unit
val grow_to_by_double : 'a t -> int -> unit
val is_full : 'a t -> bool
val push : 'a t -> 'a -> unit
val push_none : 'a t -> unit
val last : 'a t -> 'a
val get : 'a t -> int -> 'a
val set : 'a t -> int -> 'a -> unit
val set_size : 'a t -> int -> unit
val copy : 'a t -> 'a t
val move_to : 'a t -> 'a t -> unit
val remove : 'a t -> 'a -> unit
val fast_remove : 'a t -> 'a -> unit
val sort : 'a t -> ('a -> 'a -> int) -> unit
val iter : 'a t -> ('a -> unit) -> unit
