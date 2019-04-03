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

module P = Shostak.Polynome

type solution = ((P.r * Numbers.Z.t) list)

(** Performs the cubefast test.
    Takes in argument a list of polynoms representing
    inequalities (p(X) <= 0);
    returns an integer solution if there exists an hypercube
    of length 1 inscribed in the polyhedron defined by the inequalities.
*)
val cubefast : P.t list -> (P.r * Numbers.Z.t) list option

(**
   Performs the cubefast test by maximizing the size of the square.
*)
val cubefast_k : P.t list -> ((P.r * Numbers.Z.t) list * bool) option
