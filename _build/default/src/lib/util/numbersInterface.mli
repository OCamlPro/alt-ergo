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

(** Interface of Integers **)
module type ZSig = sig
  type t
  val zero : t
  val one : t
  val m_one : t (* minus one *)

  val compare : t -> t -> int
  val compare_to_0 : t -> int
  val equal   : t -> t -> bool
  val sign : t -> int
  val hash : t -> int

  val is_zero : t -> bool
  val is_one : t -> bool
  val is_m_one : t -> bool

  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val div : t -> t -> t
  val rem : t -> t -> t
  val div_rem : t -> t -> t * t
  val minus : t -> t
  val abs  : t -> t
  val my_gcd : t -> t -> t
  val my_lcm : t -> t -> t
  val max : t -> t -> t
  val from_int : int -> t
  val from_string : string -> t
  val to_string : t -> string

  (** convert to machine integer. returns None in case of overflow *)
  val to_machine_int : t -> int option
  val to_float : t -> float
  val fdiv : t -> t -> t
  val cdiv : t -> t -> t
  val power : t -> int -> t

  val print : Format.formatter -> t -> unit

  val shift_left: t -> int -> t
  (** Shifts left by (n:int >= 0) bits. This is the same as t * pow(2,n) *)

  val sqrt_rem: t -> (t * t)
  (** returns sqrt truncated with the remainder. It assumes that the argument
      is positive, otherwise, [Invalid_argument] is raised. *)

  (** [testbit z n] returns true iff the nth bit of z is set to 1.
      n is supposed to be positive *)
  val testbit: t -> int -> bool

  (** return the number of bits set to one in the given integer *)
  val numbits : t -> int
end


(** Interface of Rationals **)
module type QSig = sig

  module Z : ZSig

  type t

  exception Not_a_float

  val num : t -> Z.t
  val den : t -> Z.t

  val zero : t
  val one : t
  val m_one : t (* minus one *)

  val compare : t -> t -> int
  val compare_to_0 : t -> int
  val equal   : t -> t -> bool
  val sign : t -> int
  val hash : t -> int

  val is_zero : t -> bool
  val is_one : t -> bool
  val is_m_one : t -> bool
  val is_int : t -> bool

  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val div : t -> t -> t
  val minus : t -> t
  val abs : t -> t
  val min : t -> t -> t
  val max : t -> t -> t
  val inv : t -> t
  (* Euclidean division's remainder. Assumes that the arguments are in Z *)
  val modulo : t -> t -> t

  val from_float : float -> t
  val from_int : int -> t
  val from_z : Z.t -> t
  val from_zz: Z.t -> Z.t -> t
  val from_string : string -> t
  val to_float : t -> float
  val to_z : t -> Z.t (* Assumes that the argument is in Z *)
  val to_string : t -> string

  val print : Format.formatter -> t -> unit

  val power : t -> int -> t
  val floor : t -> t
  val ceiling : t -> t

  val truncate : t -> Z.t
  (** converts the argument to an integer by truncation. **)

  val mult_2exp: t -> int -> t
  (** multiplies the first argument by 2^(the second argument) *)

  val div_2exp: t -> int -> t
  (** divides the first argument by 2^(the second argument) *)

end
