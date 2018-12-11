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

(* We put an ml file for the module type, to avoid issues when
   building the lib *)

module type S = sig
  type t

  exception Sat of t
  exception Unsat of Explanation.t
  exception I_dont_know of t

  (* the empty sat-solver context *)
  val empty : unit -> t
  val empty_with_inst : (Expr.t -> bool) -> t

  (* [assume env f] assume a new formula [f] in [env]. Raises Unsat if
     [f] is unsatisfiable in [env] *)
  val assume : t -> Expr.gformula -> Explanation.t -> t

  val assume_th_elt : t -> Expr.th_elt -> Explanation.t -> t

  (* [pred_def env f] assume a new predicate definition [f] in [env]. *)
  val pred_def : t -> Expr.t -> string -> Explanation.t -> Loc.t -> t

  (* [unsat env f size] checks the unsatisfiability of [f] in
     [env]. Raises I_dont_know when the proof tree's height reaches
     [size]. Raises Sat if [f] is satisfiable in [env] *)
  val unsat : t -> Expr.gformula -> Explanation.t

  val print_model : header:bool -> Format.formatter -> t -> unit

  val reset_refs : unit -> unit
  val get_steps : unit -> int64

end


module type SatContainer = sig
  module Make (Th : Theory.S) : S
end
