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
