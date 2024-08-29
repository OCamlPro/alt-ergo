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

val src : Logs.src

type 'a alpha_term = {
  bv : 'a;
  sz : int;
}

val pp_alpha_term : 'a Fmt.t -> 'a alpha_term Fmt.t

(** The ['a signed] type represents possibly negated values of type ['a]. It is
    used for [bvnot] at the leaves ([Other] and [Ext] below). *)
type 'a signed = { value : 'a ; negated : bool }

type 'a simple_term_aux =
  | Cte of Z.t
  | Other of 'a signed
  | Ext of 'a signed * int * int * int (*// id * size * i * j //*)

type 'a simple_term = ('a simple_term_aux) alpha_term

type 'a abstract = 'a simple_term list

val extract : int -> int -> int -> 'a abstract -> 'a abstract
(** [extract size i j x] extracts [i..j] from a composition of size [size].

    An element of size [sz] at the head of the composition contains the bits
    [size - 1 .. size - sz] inclusive. *)

val zero_extend : int -> 'a abstract -> 'a abstract
(** [zero_extract sz bv] adds [sz] zeros to the front (high bits) of [bv]. *)

val lognot : 'a abstract -> 'a abstract

(** [to_Z_opt r] evaluates [r] to an integer if possible. *)
val to_Z_opt : 'a abstract -> Z.t option

(** [int2bv_const n z] evaluates [z] as a constant [n]-bits bitvector.

    If [z] is out of the [0 .. 2^n] range, only the first [n] bits of [z] in
    binary representation are considered, i.e.  [int2bv_const n z] is always
    equal to [int2bv_const n (erem z (1 lsl n))]. *)
val int2bv_const : int -> Z.t -> 'a abstract

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak
    (X : ALIEN) : Sig.SHOSTAK with type r = X.r and type t = X.r abstract
