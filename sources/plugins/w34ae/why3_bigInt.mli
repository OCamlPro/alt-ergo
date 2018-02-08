(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type t
(*
val compare : t -> t -> int
 *)
(** constants *)
val zero : t(*
val one : t
val of_int : int -> t

(** basic operations *)
val succ : t -> t
val pred : t -> t*)
val add_int : int -> t -> t
val mul_int : int -> t -> t(*
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val minus : t -> t
val sign : t -> int

(** comparisons *)
val eq : t -> t -> bool
val lt : t -> t -> bool
val gt : t -> t -> bool
val le : t -> t -> bool
val ge : t -> t -> bool

(** Division and modulo operators with the convention
that modulo is always non-negative.

It implies that division rounds down when divisor is positive, and
rounds up when divisor is negative.
*)
val euclidean_div_mod : t -> t -> t * t
val euclidean_div : t -> t -> t
val euclidean_mod : t -> t -> t

(** "computer" division, i.e division rounds towards zero, and thus [mod
    x y] has the same sign as x
*)
val computer_div_mod : t -> t -> t * t
val computer_div : t -> t -> t
val computer_mod : t -> t -> t

(** min, max, abs *)
val min : t -> t -> t
val max : t -> t -> t
val abs : t -> t

(** number of digits  *)
val num_digits : t -> int

(** power of small integers. Second arg must be non-negative *)
val pow_int_pos : int -> int -> t
val pow_int_pos_bigint : int -> t -> t

(** conversions *)
val of_string : string -> t
val to_string : t -> string
val to_int : t -> int*)
