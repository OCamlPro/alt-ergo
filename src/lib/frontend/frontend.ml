(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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

open Commands
open Format
open Options

module E = Expr
module Ex = Explanation

type used_context = Util.SS.t option

let unused_context name context =
  match context with
  | None -> false
  | Some s -> not (Util.SS.mem name s)

type 'a status =
  | Unsat of Commands.sat_tdecl * Ex.t
  | Inconsistent of Commands.sat_tdecl
  | Sat of Commands.sat_tdecl * 'a
  | Unknown of Commands.sat_tdecl * 'a
  | Timeout of Commands.sat_tdecl option
  | Preprocess

let print_status status steps =
  let check_status_consistency s =
    let known_status = get_status () in
    match s with
    | Unsat _ ->
      if known_status == Status_Sat then begin
        Printer.print_wrn
          "This file is known to be Sat but Alt-Ergo return Unsat";
        Errors.warning_as_error ()
      end
    | Sat _ ->
      if known_status == Status_Unsat then begin
        Printer.print_wrn
          "This file is known to be Unsat but Alt-Ergo return Sat";
        Errors.warning_as_error ()
      end
    | Inconsistent _ | Unknown _ | Timeout _ | Preprocess ->
      assert false
  in
  let validity_mode =
    match Options.get_output_format () with
    | Smtlib2 _ -> false
    | Native | Why3 | Unknown _ -> true
  in
  let get_goal_name d =
    match d.st_decl with
    | Query(g,_,_) -> Some g
    | _ -> None
  in

  let time = Time.value() in
  match status with
  | Unsat (d, dep) ->
    let loc = d.st_loc in
    Printer.print_status_unsat ~validity_mode
      (Some loc) (Some time) (Some steps) (get_goal_name d);
    if get_unsat_core() &&
       not (get_debug_unsat_core()) &&
       not (get_save_used_context())
    then
      Printer.print_fmt (Options.Output.get_fmt_regular ())
        "unsat-core:@,%a@."
        (Ex.print_unsat_core ~tab:true) dep;
    check_status_consistency status;

  | Inconsistent d ->
    let loc = d.st_loc in
    Printer.print_status_inconsistent ~validity_mode
      (Some loc) (Some time) (Some steps) (get_goal_name d);

  | Sat (d, _) ->
    let loc = d.st_loc in
    Printer.print_status_sat ~validity_mode
      (Some loc) (Some time) (Some steps) (get_goal_name d);
    check_status_consistency status;

  | Unknown (d, _) ->
    let loc = d.st_loc in
    Printer.print_status_unknown ~validity_mode
      (Some loc) (Some time) (Some steps) (get_goal_name d);

  | Timeout (Some d) ->
    let loc = d.st_loc in
    Printer.print_status_timeout ~validity_mode
      (Some loc) (Some time) (Some steps) (get_goal_name d);

  | Timeout None ->
    Printer.print_status_timeout ~validity_mode
      None (Some time) (Some steps) None;

  | Preprocess ->
    Printer.print_status_preprocess ~validity_mode
      (Some time) (Some steps)

module type S = sig

  type sat_env

  type res = [
    | `Sat
    | `Unknown
    | `Unsat
  ]

  type env = private {
    used_context : used_context;
    consistent_dep_stack: (res * Explanation.t) Stack.t;
    sat_env : sat_env;
    mutable res : res;
    mutable expl : Explanation.t
  }

  type 'a process = ?loc : Loc.t -> 'a -> env -> unit

  val init_env : ?sat_env:sat_env -> used_context -> env

  val push : int process

  val pop : int process

  val assume : (string * E.t * bool) process

  val pred_def : (string * E.t) process

  val query : (string * E.t * Ty.goal_sort) process

  val th_assume : E.th_elt process

  val optimize : Objective.Function.t process

  val process_decl:
    ?hook_on_status: (sat_env status -> int -> unit) ->
    env ->
    sat_tdecl ->
    unit

  val print_model: sat_env Fmt.t
end

let init_with_replay_used acc f =
  assert (Sys.file_exists f);
  let cin = open_in f in
  let acc = ref (match acc with None -> Util.SS.empty | Some ss -> ss) in
  try
    while true do acc := Util.SS.add (input_line cin) !acc done;
    assert false
  with End_of_file ->
    Some !acc

let init_used_context ~goal_name =
  if Options.get_replay_used_context () then
    let uc_f =
      sprintf "%s.%s.used" (Options.get_used_context_file ()) goal_name
    in
    if Sys.file_exists uc_f then init_with_replay_used None uc_f
    else
      begin
        Printer.print_wrn
          "File %s not found! Option -replay-used will be ignored" uc_f;
        None
      end
  else
    None

let init_all_used_context () =
  if Options.get_replay_all_used_context () then
    let dir = Filename.dirname (Options.get_used_context_file ()) in
    Array.fold_left
      (fun acc f ->
         let f = sprintf "%s/%s" dir f in
         if (Filename.check_suffix f ".used") then init_with_replay_used acc f
         else acc
      ) None (Sys.readdir dir)
  else None

let choose_used_context all_ctxt ~goal_name =
  if Options.get_replay_all_used_context () then all_ctxt
  else init_used_context ~goal_name


module Make(SAT : Sat_solver_sig.S) : S with type sat_env = SAT.t = struct

  type sat_env = SAT.t

  type res = [
    | `Sat
    | `Unknown
    | `Unsat
  ]

  type env = {
    used_context : used_context;
    consistent_dep_stack: (res * Explanation.t) Stack.t;
    sat_env : sat_env;
    mutable res : res;
    mutable expl : Explanation.t
  }

  type 'a process = ?loc : Loc.t -> 'a -> env -> unit

  let init_env ?(sat_env=SAT.empty ()) used_context =
    {
      used_context;
      consistent_dep_stack = Stack.create ();
      sat_env;
      res = `Unknown;
      expl = Explanation.empty
    }

  let output_used_context g_name dep =
    if not (Options.get_js_mode ()) then begin
      let f = Options.get_used_context_file () in
      let cout = open_out (sprintf "%s.%s.used" f g_name) in
      let cfmt = Format.formatter_of_out_channel cout in
      Ex.print_unsat_core cfmt dep;
      close_out cout
    end

  let check_produced_unsat_core dep =
    if get_verbose () then
      Printer.print_dbg
        ~module_name:"Frontend"
        ~function_name:"check_produced_unsat_core"
        "@[<v 0>checking the unsat-core:@,-------------------@,@]%a"
        (Ex.print_unsat_core ~tab:false) dep;
    try
      let pb = E.Set.elements (Ex.formulas_of dep) in
      let satenv = SAT.empty () in
      let () =
        List.iter
          (fun f ->
             SAT.assume satenv
               {E.ff=f;
                origin_name = "";
                gdist = -1;
                hdist = -1;
                trigger_depth = max_int;
                nb_reductions = 0;
                age=0;
                lem=None;
                mf=false;
                gf=false;
                from_terms = [];
                theory_elim = true;
               } Ex.empty
          )
          pb
      in
      ignore (SAT.unsat
                satenv
                {E.ff=E.vrai;
                 origin_name = "";
                 gdist = -1;
                 hdist = -1;
                 trigger_depth = max_int;
                 nb_reductions = 0;
                 age=0;
                 lem=None;
                 mf=false;
                 gf=false;
                 from_terms = [];
                 theory_elim = true;
                });
      Errors.run_error Errors.Failed_check_unsat_core
    with
    | SAT.Unsat _  -> ()
    | (SAT.Sat | SAT.I_dont_know) as e -> raise e

  let mk_root_dep name f loc =
    if Options.get_unsat_core () then Ex.singleton (Ex.RootDep {name;f;loc})
    else Ex.empty

  let internal_decl ?(loc = Loc.dummy) (id : Id.typed) (env : env) : unit =
    ignore loc;
    match env.res with
    | `Sat | `Unknown ->
      SAT.declare env.sat_env id
    | `Unsat -> ()

  let internal_push ?(loc = Loc.dummy) (n : int) (env : env) : unit =
    ignore loc;
    Util.loop ~f:(fun _ res () -> Stack.push res env.consistent_dep_stack)
      ~max:n ~elt:(env.res, env.expl) ~init:();
    Steps.apply_without_step_limit (fun () -> SAT.push env.sat_env n)

  let internal_pop ?(loc = Loc.dummy) (n : int) (env : env) : unit =
    ignore loc;
    let res, expl =
      Util.loop ~f:(fun _n () _env -> Stack.pop env.consistent_dep_stack)
        ~max:n ~elt:() ~init:(env.res, env.expl)
    in
    SAT.pop env.sat_env n;
    env.res <- res;
    env.expl <- expl

  let internal_assume
      ?(loc = Loc.dummy)
      ((name, f, mf) : string * E.t * bool)
      (env : env) =
    let is_hyp = try (Char.equal '@' name.[0]) with _ -> false in
    if is_hyp || not (unused_context name env.used_context) then
      let expl =
        if is_hyp then
          Ex.empty
        else
          mk_root_dep name f loc
      in
      match env.res with
      | `Sat | `Unknown ->
        SAT.assume env.sat_env
          {E.ff=f;
           origin_name = name;
           gdist = -1;
           hdist = (if is_hyp then 0 else -1);
           trigger_depth = max_int;
           nb_reductions = 0;
           age=0;
           lem=None;
           mf=mf;
           gf=false;
           from_terms = [];
           theory_elim = true;
          }
          expl;
        env.expl <- expl;
      | `Unsat ->
        env.expl <- expl

  let internal_pred_def ?(loc = Loc.dummy) (name, f) env =
    if not (unused_context name env.used_context) then
      let expl = mk_root_dep name f loc in
      SAT.pred_def env.sat_env f name expl loc;
      env.expl <- expl

  let internal_query ?(loc = Loc.dummy) (n, f, sort) env =
    ignore loc;
    let expl =
      match env.res with
      | `Sat | `Unknown ->
        let expl' = SAT.unsat env.sat_env
            {E.ff=f;
             origin_name = n;
             hdist = -1;
             gdist = 0;
             trigger_depth = max_int;
             nb_reductions = 0;
             age=0;
             lem=None;
             mf=(sort != Ty.Check);
             gf=true;
             from_terms = [];
             theory_elim = true;
            }
        in
        Ex.union expl' env.expl
      | `Unsat -> env.expl
    in
    if get_debug_unsat_core () then check_produced_unsat_core expl;
    if get_save_used_context () then output_used_context n expl;
    env.res <- `Unsat;
    env.expl <- expl

  let internal_th_assume
      ?(loc = Loc.dummy)
      ({ Expr.ax_name; Expr.ax_form ; _ } as th_elt)
      env =
    if not (unused_context ax_name env.used_context) then
      match env.res with
      | `Sat | `Unknown ->
        let expl = mk_root_dep ax_name ax_form loc in
        SAT.assume_th_elt env.sat_env th_elt expl;
        env.expl <- expl
      | `Unsat -> ()

  let internal_optimize ?(loc = Loc.dummy) fn env =
    ignore loc;
    match env.res with
    | `Sat | `Unknown ->
      SAT.optimize env.sat_env fn
    | `Unsat -> ()

  (** Checks whether the env can be used before actually calling the
      function. *)
  let check_if_over f env =
    match SAT.get_unknown_reason env.sat_env with
    | Some (Step_limit _ | Timeout _) -> ()
    | _ -> f env

  let handle_sat_exn f ?loc x env =
    try f ?loc x env with
    | SAT.Sat -> env.res <- `Sat
    | SAT.Unsat expl ->
      env.res <- `Unsat;
      env.expl <- Ex.union expl env.expl
    | SAT.I_dont_know ->
      env.res <- `Unknown

  (* Wraps the function f to check if the step limit is reached (in which case,
     don't do anything), and then calls the function & catches the
     exceptions. *)
  let wrap_f f ?loc x env =
    check_if_over (handle_sat_exn f ?loc x) env

  let push = wrap_f internal_push

  let pop = wrap_f internal_pop

  let assume = wrap_f internal_assume

  let pred_def = wrap_f internal_pred_def

  let query = wrap_f internal_query

  let th_assume = wrap_f internal_th_assume

  let optimize = wrap_f internal_optimize

  let process_decl ?(hook_on_status=(fun _ -> ignore)) env d =
    try
      match d.st_decl with
      | Decl id -> check_if_over (internal_decl ~loc:d.st_loc id) env
      | Push n -> check_if_over (internal_push ~loc:d.st_loc n) env
      | Pop n -> check_if_over (internal_pop ~loc:d.st_loc n) env
      | Assume (n, f, mf) ->
        check_if_over (internal_assume ~loc:d.st_loc (n, f, mf)) env
      | PredDef (f, name) ->
        check_if_over (internal_pred_def ~loc:d.st_loc (name, f)) env
      | RwtDef _ -> assert false
      | Query (n, f, sort) ->
        begin
          (* If we have reached an unknown state, we can return it right
             away. *)
          match SAT.get_unknown_reason env.sat_env with
          | Some (Step_limit _ | Timeout _)  -> raise SAT.I_dont_know
          | Some _ ->
            (* For now, only the step limit is an unknown step reachable
               here. We could raise SAT.I_dont_know as in the previous case,
               but we have choosen a defensive strategy. *)
            assert false
          | None ->
            internal_query ~loc:d.st_loc (n, f, sort) env;
            match env.res with
            | `Unsat ->
              hook_on_status (Unsat (d, env.expl)) (Steps.get_steps ())
            | _ -> assert false
        end
      | ThAssume th_elt ->
        check_if_over (internal_th_assume ~loc:d.st_loc th_elt) env
      | Optimize fn ->
        check_if_over (internal_optimize ~loc:d.st_loc fn) env
    with
    | SAT.Sat ->
      (* This case should mainly occur when a query has a non-unsat result,
         so we want to print the status in this case. *)
      hook_on_status (Sat (d, env.sat_env)) (Steps.get_steps ());
      env.res <- `Sat

    | SAT.Unsat expl' ->
      (* This case should mainly occur when a new assumption results in an unsat
         env, in which case we do not want to print status, since the correct
         status should be printed at the next query. *)
      let expl = Ex.union env.expl expl' in
      if get_debug_unsat_core () then check_produced_unsat_core expl;
      (* print_status (Inconsistent d) (Steps.get_steps ()); *)
      env.res <- `Unsat;
      env.expl <- expl

    | SAT.I_dont_know ->
      (* TODO: always print Unknown for why3 ? *)
      let ur = SAT.get_unknown_reason env.sat_env in
      let status =
        match ur with
        | Some (Sat_solver_sig.Timeout _) -> Timeout (Some d)
        | _ -> Unknown (d, env.sat_env)
      in
      hook_on_status status (Steps.get_steps ());
      (* TODO: Is it an appropriate behaviour? *)
      (*       if timeout != NoTimeout then raise Util.Timeout; *)
      env.res <- `Unknown

    | Util.Timeout as e ->
      (* In this case, we obviously want to print the status,
         since we exit right after  *)
      hook_on_status (Timeout (Some d)) (Steps.get_steps ());
      raise e

  let print_model ppf env =
    match SAT.get_model env with
    | None ->
      let ur = SAT.get_unknown_reason env in
      Printer.print_fmt (Options.Output.get_fmt_diagnostic ())
        "@[<v 0>It seems that no model has been computed so \
         far. You may need to change your model generation strategy \
         or to increase your timeouts. \
         Returned unknown reason = %a@]"
        Sat_solver_sig.pp_ae_unknown_reason_opt ur;
      Fmt.pf ppf "()"

    | Some model ->
      Models.pp ppf model
end
