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

module Combine : Sig.X

module Polynome : Polynome.T
  with type r = Combine.r

module Arith : Sig.SHOSTAK
  with type r = Combine.r and type t = Polynome.t

module Records : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Records.abstract

module Bitv : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Bitv.abstract

module Arrays : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Arrays.abstract

module Enum : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Enum.abstract

module Adt : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Adt.abstract

module Ite : Sig.SHOSTAK
  with type r = Combine.r and type t = Combine.r Ite.abstract

module Ac : Ac.S with type r = Combine.r and type t = Combine.r Sig.ac

