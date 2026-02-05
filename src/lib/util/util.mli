(******************************************************************************)
(*                                                                            *)
(*  Alt-Ergo: The SMT Solver For Software Verification                        *)
(*  Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                            *)
(*  This software is governed by the CeCILL  license under French law and     *)
(*  abiding by the rules of distribution of free software.  You can  use,     *)
(*  modify and/ or redistribute the software under the terms of the CeCILL    *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*  "http://www.cecill.info".                                                 *)
(*                                                                            *)
(*  As a counterpart to the access to the source code and  rights to copy,    *)
(*  modify and redistribute granted by the license, users are provided only   *)
(*  with a limited warranty  and the software's author,  the holder of the    *)
(*  economic rights,  and the successive licensors  have only  limited        *)
(*  liability.                                                                *)
(*                                                                            *)
(*  In this respect, the user's attention is drawn to the risks associated    *)
(*  with loading,  using,  modifying and/or developing or reproducing the     *)
(*  software by the user in light of its specific status of free software,    *)
(*  that may mean  that it is complicated to manipulate,  and  that  also     *)
(*  therefore means  that it is reserved for developers  and  experienced     *)
(*  professionals having in-depth computer knowledge. Users are therefore     *)
(*  encouraged to load and test the software's suitability as regards their   *)
(*  requirements in conditions enabling the security of their systems and/or  *)
(*  data to be ensured and,  more generally, to use and operate it in the     *)
(*  same conditions as regards security.                                      *)
(*                                                                            *)
(*  The fact that you are presently reading this means that you have had      *)
(*  knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*  The latest releases of Alt-Ergo are distributed under the terms of        *)
(*  OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  The Alt-Ergo theorem prover                                               *)
(*                                                                            *)
(*  Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*  Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                            *)
(*  CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*  More details can be found in the directory licenses/                      *)
(*                                                                            *)
(******************************************************************************)

exception Timeout
exception Unsolvable

exception Cmp of int

module MI : Map.S with type key = int
module SI : Set.S with type elt = int
module SS : Set.S with type elt = string

(** Different values for -case-split-policy option:
    -after-theory-assume (default value): after assuming facts in
    theory by the SAT
    -before-matching: just before performing a matching round
    -after-matching: just after performing a matching round **)
type case_split_policy =
  | AfterTheoryAssume (* default *)
  | BeforeMatching
  | AfterMatching


type inst_kind = Normal | Forward | Backward

type sat_solver =
  | Tableaux
  | Tableaux_CDCL
  | CDCL
  | CDCL_Tableaux

type theories_extensions =
  | Sum
  | Adt
  | Arrays
  | Records
  | Bitv
  | LIA
  | LRA
  | NRA
  | NIA
  | FPA

type axiom_kind = Default | Propagator

val th_ext_of_string : string -> theories_extensions option
val string_of_th_ext : theories_extensions -> string

(**
   generic function for comparing algebraic data types.
   [compare_algebraic a b f]
   - Stdlib.compare a b is used if

*)
val [@inline always] compare_algebraic : 'a -> 'a -> (('a * 'a) -> int) -> int

val [@inline always] cmp_lists: 'a list -> 'a list -> ('a -> 'a -> int) -> int

type matching_env =
  {
    nb_triggers : int;
    triggers_var : bool;
    no_ematching: bool;
    greedy : bool;
    use_cs : bool;
    backward : inst_kind
  }

(** Loops from 0 to [max] and returns
    [(f max elt ... (f 1 elt (f 0 elt init)))...)].
    Returns [init] if [max] < 0
*)
val loop:
  f : (int -> 'a -> 'b -> 'b) ->
  max : int ->
  elt : 'a ->
  init : 'b ->
  'b

val print_list:
  sep:string ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit

val print_list_pp:
  sep:(Format.formatter -> unit -> unit) ->
  pp:(Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit
