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

open Typed
open Commands
open Format
open Options

module E = Expr
module Ex = Explanation
module type S = sig

  type sat_env
  type used_context

  type status =
    | Unsat of Commands.sat_tdecl * Ex.t
    | Inconsistent of Commands.sat_tdecl
    | Sat of Commands.sat_tdecl * sat_env
    | Unknown of Commands.sat_tdecl * sat_env
    | Timeout of Commands.sat_tdecl option
    | Preprocess

  val process_decl:
    (status -> int -> unit) ->
    used_context -> Util.SS.t ->
    (bool * Ex.t) Stack.t ->
    sat_env * bool * Ex.t ->
    Commands.sat_tdecl ->
    sat_env * bool * Ex.t

  val print_status : status -> int -> unit

  val init_all_used_context : unit -> used_context
  val choose_used_context : used_context -> goal_name:string -> used_context

end

module Make(SAT : Sat_solver_sig.S) : S with type sat_env = SAT.t = struct

  type sat_env = SAT.t

  type used_context = Util.SS.t option

  type status =
    | Unsat of Commands.sat_tdecl * Ex.t
    | Inconsistent of Commands.sat_tdecl
    | Sat of Commands.sat_tdecl * sat_env
    | Unknown of Commands.sat_tdecl * sat_env
    | Timeout of Commands.sat_tdecl option
    | Preprocess

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
      let env =
        List.fold_left
          (fun env f ->
             SAT.assume env
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
          ) (SAT.empty ()) pb
      in
      ignore (SAT.unsat
                env
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
    | (SAT.Sat _ | SAT.I_dont_know _) as e -> raise e


  let unused_context name context =
    match context with
    | None -> false
    | Some s -> not (Util.SS.mem name s)

  let mk_root_dep name f loc =
    if Options.get_unsat_core () then Ex.singleton (Ex.RootDep {name;f;loc})
    else Ex.empty

  let timeout_reason_to_string = function
    | None -> "(?)"
    | Some SAT.NoTimeout -> "NoTimeout"
    | Some SAT.Assume -> "Assume"
    | Some SAT.ProofSearch -> "ProofSearch"
    | Some SAT.ModelGen -> "ModelGen"

  let print_model ?(all_sat=false) used_logics model_opt timeout =
    let pp_prop_model = all_sat || Options.get_show_prop_model () in
    let get_m = Options.get_interpretation () || pp_prop_model in
    let s = timeout_reason_to_string timeout in
    match model_opt with
    | None ->
      if get_m then
        Printer.print_fmt (Options.get_fmt_err ())
          "@[<v 0>It seems that no model has been computed so \
           far. You may need to change your model generation strategy \
           or to increase your timeouts. Returned timeout reason = %s@]" s

    | Some m ->
      assert (get_m);
      if get_m then
        Printer.print_dbg "@[<v 0>; Returned timeout reason = %s@]" s;
      let m = Lazy.force m in
      Models.output_concrete_model ~used_logics ~pp_prop_model
        (get_fmt_mdl ()) m

  let filter_by_all_sat propositional filter =
    if filter == E.Set.empty then propositional
    else
      E.Set.filter
        (fun t ->
           E.Set.mem t filter || E.Set.mem (E.neg t) filter
        )propositional

  let rec process_decl print_status used_context used_names
      consistent_dep_stack ((env, consistent, dep) as acc) d =
    try
      match d.st_decl with
      | Push n ->
        Util.loop ~f:(fun _n env () -> Stack.push env consistent_dep_stack)
          ~max:n ~elt:(consistent,dep) ~init:();
        SAT.push env n, consistent, dep
      | Pop n ->
        let consistent,dep =
          Util.loop ~f:(fun _n () _env -> Stack.pop consistent_dep_stack)
            ~max:n ~elt:() ~init:(consistent,dep)
        in
        SAT.pop env n, consistent, dep
      | Assume(n, f, mf) ->
        let is_hyp = try (Char.equal '@' n.[0]) with _ -> false in
        if not is_hyp && unused_context n used_context then
          acc
        else
          let dep = if is_hyp then Ex.empty else mk_root_dep n f d.st_loc in
          if consistent then
            SAT.assume env
              {E.ff=f;
               origin_name = n;
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
              } dep,
            consistent, dep
          else env, consistent, dep
      | PredDef (f, name) ->
        if unused_context name used_context then acc
        else
          let dep = mk_root_dep name f d.st_loc in
          SAT.pred_def env f name dep d.st_loc, consistent, dep

      | RwtDef _ -> assert false

      | Query(n, f, sort) ->
        let dep =
          if consistent then
            let dep' = SAT.unsat env
                {E.ff=f;
                 origin_name = n;
                 hdist = -1;
                 gdist = 0;
                 trigger_depth = max_int;
                 nb_reductions = 0;
                 age=0;
                 lem=None;
                 mf=(sort != Check);
                 gf=true;
                 from_terms = [];
                 theory_elim = true;
                } in
            Ex.union dep' dep
          else dep
        in
        if get_debug_unsat_core () then check_produced_unsat_core dep;
        if get_save_used_context () then output_used_context n dep;
        print_status (Unsat (d, dep)) (Steps.get_steps ());
        env, false, dep

      | ThAssume ({ Expr.ax_name; Expr.ax_form ; _ } as th_elt) ->
        if unused_context ax_name used_context then
          acc
        else
        if consistent then
          let dep = mk_root_dep ax_name ax_form d.st_loc in
          let env = SAT.assume_th_elt env th_elt dep in
          env, consistent, dep
        else env, consistent, dep

    with
    | SAT.Sat t ->
      print_status (Sat (d,t)) (Steps.get_steps ());
      process_unknown
        print_status used_context used_names consistent_dep_stack
        env dep d SAT.NoTimeout

    | SAT.Unsat dep' ->
      let dep = Ex.union dep dep' in
      if get_debug_unsat_core () then check_produced_unsat_core dep;
      print_status (Inconsistent d) (Steps.get_steps ());
      env , false, dep

    | SAT.I_dont_know {env; timeout} ->
      (* TODO: always print Unknown for why3 ? *)
      let status =
        if timeout != NoTimeout && (not (get_timeout_as_unknwon ())) then
          (Timeout (Some d))
        else (Unknown (d, env))
      in
      print_status status (Steps.get_steps ());
      process_unknown
        print_status used_context used_names consistent_dep_stack
        env dep d timeout

    | Util.Timeout as e ->
      print_status (
        if get_timeout_as_unknwon () then
          (Unknown (d, env))
        else Timeout (Some d))
        (Steps.get_steps ());
      (* dont call 'process_unknown' in this case. Timeout stops
         all-models listing *)
      print_model used_names (SAT.get_model env) None;
      raise e

  and process_unknown print_status used_context used_names consistent_dep_stack
      env dep d timeout_kind =
    match d.st_decl with
    | Assume _ | PredDef _ | RwtDef _ | Push _ | Pop _ | ThAssume _->
      (* cannot raise Sat or Unknown in this case *)
      assert false

    | Query(n, _, sort) ->
      (* 1. check if we are in all-sat mode, and build the filter
         that'll be applied on the boolean model *)
      let all_sat_mode =
        match sort with
        | AllSat l ->
          (* 1.A SMT command check-all-sat *)
          Some (List.fold_left
                  (fun acc s ->
                     (*transform string to propositional vars (E.t)*)
                     let t = E.mk_term (Symbols.name s) [] Ty.Tbool in
                     E.Set.add t acc
                  )E.Set.empty l)

        | Thm | Sat ->
          (* 1.B if user rather set option --alll-models: empty
             filter. Otherwise, all_sat_mode = None *)
          if Options.get_all_models () then Some E.Set.empty
          else None

        | Cut | Check ->
          (* 1.3 all_sat_mode = None for cut and check *)
          None
      in
      let m = match SAT.get_model env with
        | None ->
          if all_sat_mode != None then
            (* all-sat enabled but interpretation disabled. No timeout
               here! Return a model with just the propositional part
            *)
            Some (lazy {
                Models.propositional = SAT.get_propositional_model env;
                constants = Profile.P.empty;
                functions = Profile.P.empty;
                arrays = Profile.P.empty;
                objectives = Util.MI.empty;
                terms_values = Expr.Map.empty }
              )
          else
            None
        | Some _ as md -> md
      in
      match m, all_sat_mode with
      | Some m, Some filter ->
        (* 1. case where all-bool-models wrt. given filter is
           requested *)
        let m = Lazy.force m in
        let propositional = filter_by_all_sat m.propositional filter in
        let m = { m with propositional } in
        print_model ~all_sat:true used_names
          (Some (lazy m)) (Some timeout_kind);
        (* we build the conjunction that corresponds to the current
           filtered model *)
        let f =
          Expr.Set.fold
            (fun e acc -> E.mk_and e acc false 0) propositional E.vrai
        in
        if E.equal f E.vrai then
          begin
            (* this may happen if current propositional model is empty
               (for instance, in case of timeout and no model computed
               so far). We should stop to avoid infinite loop *)
            if timeout_kind != NoTimeout then raise Util.Timeout;
            env , true, dep
          end
        else
          (* we negate and propagate the current filtered boolean model
             to force the SAT to explore other branches *)
          let d = { d with st_decl = Query(n, E.neg f, sort) } in
          (* re-set timelimit *)
          Options.Time.set_timeout
            ~is_gui:(Options.get_is_gui()) (Options.get_timelimit ());
          let env = SAT.reset_last_saved_model env in
          process_decl print_status used_context used_names
            consistent_dep_stack (env, true, dep) d

      | _ ->
        (* 2. default case + case where a simple interpretation is
           requested *)
        print_model used_names m (Some timeout_kind);
        env , true, dep

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
      | Smtlib2 -> false
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
        Printer.print_fmt (Options.get_fmt_usc ())
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
      if Options.get_interpretation () &&
         Options.get_output_format () == Why3 then begin
        Printer.print_wrn "Timeout";
        let loc = d.st_loc in
        Printer.print_status_unknown ~validity_mode
          (Some loc) (Some time) (Some steps) (get_goal_name d);
      end
      else
        let loc = d.st_loc in
        Printer.print_status_timeout ~validity_mode
          (Some loc) (Some time) (Some steps) (get_goal_name d);

    | Timeout None ->
      if Options.get_interpretation () &&
         Options.get_output_format () == Why3 then begin
        Printer.print_wrn "Timeout";
        Printer.print_status_unknown ~validity_mode
          None (Some time) (Some steps) None;
      end
      else
        Printer.print_status_timeout ~validity_mode
          None (Some time) (Some steps) None;

    | Preprocess ->
      Printer.print_status_preprocess ~validity_mode
        (Some time) (Some steps)






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

end
