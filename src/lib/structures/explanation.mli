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

type t

type rootdep = { name : string; f : Expr.t; loc : Loc.t}
type exp =
  | Literal of Satml_types.Atom.atom
  | Fresh of int
  | Bj of Expr.t
  | Dep of Expr.t
  | RootDep of rootdep

exception Inconsistent of t * Expr.Set.t list

val empty : t

val is_empty : t -> bool

val mem : exp -> t -> bool

val singleton : exp -> t

val union : t -> t -> t

val merge : t -> t -> t

val iter_atoms : (exp -> unit)  -> t -> unit

val fold_atoms : (exp -> 'a -> 'a )  -> t -> 'a -> 'a

val fresh_exp : unit -> exp

val exists_fresh : t -> bool
(** Does there exists a [Fresh _] exp in an explanation set. *)

val remove_fresh : exp -> t -> t option

val remove : exp -> t -> t

val add_fresh : exp -> t -> t

val print : Format.formatter -> t -> unit

val get_unsat_core : t -> rootdep list

val print_unsat_core : ?tab:bool -> Format.formatter -> t -> unit

val formulas_of : t -> Expr.Set.t

val bj_formulas_of : t -> Expr.Set.t

module MI : Map.S with type key = int

val literals_ids_of : t -> int MI.t

val make_deps : Expr.Set.t -> t

val has_no_bj : t -> bool

val compare : t -> t -> int

val subset : t -> t -> bool
