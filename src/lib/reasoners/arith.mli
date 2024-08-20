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

(** [calc_power x y t] Compute x^y. Raise Exit if y is not an Int
    (castable in Int). *)
val calc_power : Numbers.Q.t -> Numbers.Q.t -> Ty.t -> Numbers.Q.t

(** Same as calc_power but return an option.
    Return None if the exception Exit is raised by calc_power *)
val calc_power_opt : Numbers.Q.t -> Numbers.Q.t -> Ty.t -> Numbers.Q.t option

module Type (X : Sig.X ): Polynome.T with type r = X.r

module Shostak
    (X : Sig.X)
    (P : Polynome.EXTENDED_Polynome with type r = X.r) : Sig.SHOSTAK
  with type r = X.r and type t = P.t

(*
module Relation
    (X : Sig.X)
    (Uf : Uf.S with type r = X.r)
    (P : Polynome.EXTENDED_Polynome with type r = X.r)
  : Sig.RELATION
    with type r = X.r and type uf = Uf.t
*)
