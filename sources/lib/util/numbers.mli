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

(** Integers implementation. **)
module Z : NumbersInterface.ZSig

(** Rationals implementation. **)
module Q : sig
  include NumbersInterface.QSig with module Z = Z

  (* computing root and sqrt by default and "by excess". The given
     rational is supposed to be positive. The integer provided for
     root_xxx is also supposed to be positive. Computations use
     floats. None is returned in case of failure. sqrt_xxx versions
     are more accurate and faster than their equivalent root_xxx when
     the integer is 2*)
  val root_default : t -> int -> t option
  val root_excess  : t -> int -> t option
  val sqrt_default : t -> t option
  val sqrt_excess  : t -> t option
end
