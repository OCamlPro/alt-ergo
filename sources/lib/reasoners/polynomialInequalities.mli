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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

module type S = sig

  module P : Polynome.EXTENDED_Polynome

  (* Raises Intervals.NotConsistent expl if it manages to prove that
     the semi-algebraic set defined by polynomial inequalities in
     [env] is empty. *)
  val test_polynomes : (P.t * Intervals.t) list -> unit
end

module type Container_SIG = sig
  module Make
    (X : Sig.X)
    (Uf : Uf.S with type r = X.r)
    (P : Polynome.EXTENDED_Polynome with type r = X.r)
    : S with module P = P
end

val get_current : unit -> (module Container_SIG)
(** returns the current activated 'polynomial inequalities
    reasoner'. The default value is doing nothing.  When the selected
    reasoner is an external plugin, the first call of this function
    will attemp to dynamically load it **)

val set_current : (module Container_SIG) -> unit
(** sets a new 'polynomial inequalities reasoner'. This function is
    intended to be used by dynamically loaded plugins **)
