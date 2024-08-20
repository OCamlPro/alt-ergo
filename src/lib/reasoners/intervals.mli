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

open Intervals_intf

val src : Logs.src

val map_bound : ('a -> 'b) -> 'a bound -> 'b bound
(** [map_bound f b] applies [f] to a finite (open or closed) bound [b] and
    does not change an unbounded bound. *)

(** This module provides implementations of union-of-intervals over reals and
    integers. *)

type 'a union
(** Polymorphic union type. This allows writing conversion functions between
    integer and real unions. *)

module Real : AlgebraicField
  with type explanation := Explanation.t
   and type value := Q.t
   and type 'a union = 'a union
(** Union-of-intervals over real numbers. *)

(** Union-of-intervals over integers. *)
module Int : sig
  include EuclideanRing
    with type explanation := Explanation.t
     and type value := Z.t
     and type 'a union = 'a union

  (** {2 Bit-vector helpers}

      These functions are intended for the BV theory. They can only be used
      with integer intervals. Some of these functions return intervals "of
      width [n]", where [n] is computed from the parameters of the
      function. This means that the returned interval is contained in the
      range [[0, n)] ([0] inclusive, [n] exclusive). *)

  val lognot : t -> t
  (** Bitwise logical negation. [lognot u] always returns [-u - 1]. *)

  val extract : t -> ofs:int -> len:int -> t
  (** [extract s i j] returns the bits of [s] from position [i] to [j],
      inclusive.

      Represents the function [fun x -> floor(x / 2^i) % 2^(j - i + 1)].

      Requires [0 <= i <= j] and returns an interval of width [j - i + 1].

      {b Note}: The interval [s] must be an integer interval, but is
      allowed to be unbounded (in which case [extract s i j] returns the
      full interval [[0, 2^(j - i + 1) - 1]]). *)

  val bvudiv : size:int -> t -> t -> t
  (** [bvudiv sz s t] computes an overapproximation of integer division for
      bit-vectors of width [sz] as defined in the FixedSizeBitVectors SMT-LIB
      theory, i.e. where [bvudiv n 0] is [2^sz - 1].

      [s] and [t] must be within the [0, 2^sz - 1] range. *)

  val bvurem : t -> t -> t
  (** [bvurem sz s t] computes an overapproximation of integer remainder for
      bit-vectors of width [sz] as defined in the FixedSizeBitVectors SMT-LIB
      theory, i.e. where [bvurem n 0] is [n].

      [s] and [t] must be within the [0, 2^sz - 1] range. *)

  val bvshl : size:int -> t -> t -> t
  (** [shl sz s t] computes an overapproximation of the left shift [s lsl t],
      truncating the result to [sz] bits.

      [s] and [t] must only contain non-negative integers. *)

  val lshr : t -> t -> t
  (** [lshr s t] computes an approximation of the logical right shift [s lsr t].

      Note that the result of logical right shift is independent of bit width.

      [s] and [t] must only contain non-negative integers. *)
end

module Legacy : sig
  (** The [Legacy] module reimplements (most of) the old legacy [Intervals]
      module on top of the current implementation to ease the transition. *)

  type t

  exception NotConsistent of Explanation.t
  exception No_finite_bound

  val undefined : Ty.t -> t

  val point : Numbers.Q.t -> Ty.t -> Explanation.t -> t

  val doesnt_contain_0 : t -> Th_util.answer

  val is_strict_smaller : t -> t -> bool

  val new_borne_sup : Explanation.t -> Numbers.Q.t -> is_le : bool -> t -> t

  val new_borne_inf : Explanation.t -> Numbers.Q.t -> is_le : bool -> t -> t

  val only_borne_sup : t -> t
  (** Keep only the upper bound of the interval,
      setting the lower bound to minus infty. *)

  val only_borne_inf : t -> t
  (** Keep only the lower bound of the interval,
      setting the upper bound to plus infty. *)

  val is_point : t -> (Numbers.Q.t * Explanation.t) option

  val intersect : t -> t -> t

  val exclude : ?ex:Explanation.t -> Q.t -> t -> t

  val mult : t -> t -> t

  val power : int -> t -> t

  val root : int -> t -> t

  val add : t -> t -> t

  val scale : Numbers.Q.t -> t -> t

  val affine_scale : const:Numbers.Q.t -> coef:Numbers.Q.t -> t -> t
  (** Perform an affine transformation on the given bounds.
      Supposing input bounds (b1, b2), this will return
      (const + coef * b1, const + coef * b2).
      This function is useful to avoid the incorrect roundings that
      can take place when scaling down an integer range.

      @raise Invalid_argument if [coef] is zero. *)

  val pretty_print : t Fmt.t

  val print : t Fmt.t

  val finite_size : t -> Numbers.Q.t option

  val integer_hull :
    t ->
    (Numbers.Z.t * Explanation.t) option *
    (Numbers.Z.t * Explanation.t) option

  val borne_inf : t -> Numbers.Q.t * Explanation.t * bool
  (** bool is true when bound is large. Raise: No_finite_bound if no
      finite lower bound *)

  val borne_sup : t -> Numbers.Q.t * Explanation.t * bool
  (** bool is true when bound is large. Raise: No_finite_bound if no
      finite upper bound*)

  val div : t -> t -> t

  val coerce : Ty.t -> t -> t
  (** Coerce an interval to the given type. The main use of that function is
      to round a rational interval to an integer interval. This is particularly
      useful to avoid roudning too many times when manipulating intervals that
      at the end represent an integer interval, but whose intermediate state do
      not need to represent integer intervals (e.g. computing the interval for
      an integer polynome from the intervals of the monomes). *)

  val contains : t -> Numbers.Q.t -> bool

  val add_explanation : t -> Explanation.t -> t

  val equal : t -> t -> bool

  val pick : is_max:bool -> t -> Numbers.Q.t
  (** [pick ~is_max t] returns an element of the union of intervals [t]. If
      [is_max] is [true], we pick the largest element of [t], if it exists.
      We look for the smallest element if [is_max] is [false]. *)

  val fold :
    ('a -> Q.t bound interval -> 'a) -> 'a -> t -> 'a

  type interval_matching =
    ((Numbers.Q.t * bool) option * (Numbers.Q.t * bool) option * Ty.t)
      Var.Map.t

  (** matchs the given lower and upper bounds against the given interval, and
      update the given accumulator with the constraints. Returns None if
      the matching problem is inconsistent
  *)
  val match_interval:
    Symbols.bound -> Symbols.bound -> t -> interval_matching ->
    interval_matching option
end
