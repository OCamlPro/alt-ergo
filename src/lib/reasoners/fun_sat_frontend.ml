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

  type t = {
    mutable fs_env: FS.t;
    fs_env_stack: FS.t Stack.t
  }

  let internal_empty fs_env = {
    fs_env;
    fs_env_stack = Stack.create ()
  }

  let empty ?selector () = internal_empty (FS.empty ?selector ())

  let exn_handler f env =
    try f env with
    | FS.Sat e -> env.fs_env <- e; raise Sat
    | FS.Unsat expl -> raise (Unsat expl)
    | FS.I_dont_know e -> env.fs_env <- e; raise I_dont_know


  let declare t id =
    t.fs_env <- FS.declare t.fs_env id

  (* Push and pop are not implemented with get_tableaux_cdcl, so we have to
     manually save and restore environments. *)

  let push_cdcl_tableaux t i =
    assert (i > 0);
    for _ = 1 to i do
      Stack.push t.fs_env t.fs_env_stack
    done

  let pop_cdcl_tableaux t i =
    assert (i > 0);
    let rec aux fs_env = function
      | 1 -> t.fs_env <- fs_env
      | i -> aux (Stack.pop t.fs_env_stack) (i - 1)
    in
    aux (Stack.pop t.fs_env_stack) i

  let push t i = exn_handler (fun t ->
      if Options.get_tableaux_cdcl () then
        push_cdcl_tableaux t i
      else
        t.fs_env <- FS.push t.fs_env i
    ) t

  let pop t i = exn_handler (fun env ->
      if Options.get_tableaux_cdcl () then
        pop_cdcl_tableaux env i
      else
        t.fs_env <- FS.pop t.fs_env i
    ) t

  let assume t g expl =
    exn_handler (fun t -> t.fs_env <- FS.assume t.fs_env g expl) t

  let assume_th_elt t th expl =
    exn_handler (fun t -> t.fs_env <- FS.assume_th_elt t.fs_env th expl) t

  let pred_def t expr n expl loc =
    exn_handler (fun t -> t.fs_env <- FS.pred_def t.fs_env expr n expl loc) t

  let unsat t g =
    exn_handler (fun t -> FS.unsat t.fs_env g) t

  let optimize _env ~is_max:_ _obj =
    raise (Util.Not_implemented "optimization is not supported by FunSAT.")

  let reset_refs = FS.reset_refs

  let reinit_ctx = FS.reinit_ctx

  let get_model t = FS.get_model t.fs_env

  let get_unknown_reason t = FS.get_unknown_reason t.fs_env

  let get_value t expr = FS.get_value t.fs_env expr

  let get_objectives _env =
    raise (Util.Not_implemented "optimization is not supported by FunSAT.")
end
