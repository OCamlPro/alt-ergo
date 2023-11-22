(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module Make (Th : Theory.S) : Sat_solver_sig.S = struct
  exception Sat
  exception Unsat of Explanation.t
  exception I_dont_know

  module FS = Fun_sat.Make(Th)

  type t = FS.t ref

  let empty () = ref (FS.empty ())

  let empty_with_inst f = ref (FS.empty_with_inst f)

  let exn_handler f env =
    try f !env with
    | FS.Sat e -> env := e; raise Sat
    | FS.Unsat expl -> raise (Unsat expl)
    | FS.I_dont_know e -> env := e; raise I_dont_know

  let push t i = exn_handler (fun env -> t := FS.push env i) t

  let pop t i = exn_handler (fun env -> t := FS.pop env i) t

  let assume t g expl = exn_handler (fun env -> t := FS.assume env g expl) t

  let assume_th_elt t th expl =
    exn_handler (fun env -> t := FS.assume_th_elt env th expl) t

  let pred_def t expr n expl loc =
    exn_handler (fun env -> t := FS.pred_def env expr n expl loc) t

  let unsat t g =
    exn_handler (fun env -> FS.unsat env g) t

  let reset_refs = FS.reset_refs

  let reinit_ctx = FS.reinit_ctx

  let get_model t = FS.get_model !t

  let get_unknown_reason t = FS.get_unknown_reason !t

  let get_value t expr = FS.get_value !t expr
end
