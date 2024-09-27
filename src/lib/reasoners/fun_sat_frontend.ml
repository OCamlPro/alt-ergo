(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2022-2024 --- OCamlPro SAS                           *)
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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

let src = Logs.Src.create ~doc:"Sat" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

module Make (Th : Theory.S) : Sat_solver_sig.S = struct
  open Sat_solver_sig

  module FS = Fun_sat.Make(Th)

  type t = FS.t ref

  let empty ?selector () = ref (FS.empty ?selector ())

  let exn_handler f env =
    try f !env with
    | FS.Sat e -> env := e; raise Sat
    | FS.Unsat expl -> raise (Unsat expl)
    | FS.I_dont_know e -> env := e; raise I_dont_know

  let declare t id =
    t := FS.declare !t id

  let push t i = exn_handler (fun env -> t := FS.push env i) t

  let pop t i = exn_handler (fun env -> t := FS.pop env i) t

  let assume t g expl = exn_handler (fun env -> t := FS.assume env g expl) t

  let assume_th_elt t th expl =
    exn_handler (fun env -> t := FS.assume_th_elt env th expl) t

  let pred_def t expr n expl loc =
    exn_handler (fun env -> t := FS.pred_def env expr n expl loc) t

  let unsat t g =
    exn_handler (fun env -> FS.unsat env g) t

  let optimize _env _fn =
    raise (Util.Not_implemented "optimization is not supported by FunSAT.")

  let reset_refs = FS.reset_refs

  let reinit_ctx = FS.reinit_ctx

  let get_boolean_model t = FS.get_boolean_model !t

  let get_model t = FS.get_model !t

  let get_unknown_reason t = FS.get_unknown_reason !t

  let get_objectives _env =
    raise (Util.Not_implemented "optimization is not supported by FunSAT.")

  let supports_optimization = false

  let reset_decisions _env = ()
end
