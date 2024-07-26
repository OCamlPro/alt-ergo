(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
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

(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+                                                                      +*)
(*+                                OCaml                                 +*)
(*+                                                                      +*)
(*+                        The OCaml programmers                         +*)
(*+                                                                      +*)
(*+  Copyright 2022 Institut National de Recherche en Informatique et    +*)
(*+    en Automatique.                                                   +*)
(*+                                                                      +*)
(*+  All rights reserved.  This file is distributed under the terms of   +*)
(*+  the GNU Lesser General Public License version 2.1, with the         +*)
(*+  special exception on linking described in the file LICENSE.         +*)
(*+                                                                      +*)
(*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)

type (_, _) eq = Equal : ('a, 'a) eq

module Id : sig
  type 'a t

  val make : unit -> 'a t

  val uid : 'a t -> int

  val provably_equal : 'a t -> 'b t -> ('a, 'b) eq option
end
