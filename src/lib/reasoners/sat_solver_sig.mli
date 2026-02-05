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

module type S = sig
  type t

  exception Sat of t
  exception Unsat of Explanation.t
  exception I_dont_know of t

  (** the empty sat-solver context *)
  val empty : unit -> t
  val empty_with_inst : (Expr.t -> bool) -> t

  (** [push env n] add n new assertion levels.
      A guard g is added for every expression e assumed at the current
      assertion level.
      Ie. assuming e after the push will become g -> e,
      a g will be forced to be true (but not propagated at level 0) *)
  val push : t -> int -> t

  (** [pop env n] remove an assertion level.
      Internally, the guard g introduced in the push correponsding to this pop
      will be propagated to false (at level 0) *)
  val pop : t -> int -> t

  (** [assume env f] assume a new formula [f] in [env]. Raises Unsat if
      [f] is unsatisfiable in [env] *)
  val assume : t -> Expr.gformula -> Explanation.t -> t

  (** [assume env f exp] assume a new formula [f] with the explanation [exp]
      in the theories environment of [env]. *)
  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t

  (** [pred_def env f] assume a new predicate definition [f] in [env]. *)
  val pred_def : t -> Expr.t -> string -> Explanation.t -> Loc.t -> t

  (** [unsat env f size] checks the unsatisfiability of [f] in
      [env]. Raises I_dont_know when the proof tree's height reaches
      [size]. Raises Sat if [f] is satisfiable in [env] *)
  val unsat : t -> Expr.gformula -> Explanation.t

  (** [print_model header fmt env] print propositional model and theory model
      on the corresponding fmt. *)
  val print_model : header:bool -> Format.formatter -> t -> unit

  val reset_refs : unit -> unit
end


module type SatContainer = sig
  module Make (Th : Theory.S) : S
end
