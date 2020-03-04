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
    used_context ->
    sat_env * bool * Ex.t -> Commands.sat_tdecl ->
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
    if not (Options.js_mode ()) then begin
      let f = Options.get_used_context_file () in
      let cout = open_out (sprintf "%s.%s.used" f g_name) in
      let cfmt = Format.formatter_of_out_channel cout in
      Ex.print_unsat_core cfmt dep;
      close_out cout
    end

  let check_produced_unsat_core dep =
    if verbose () then
      fprintf fmt "checking the unsat-core:\n-------------------\n%a@."
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
      fprintf fmt "Checking produced unsat-core failed!@.";
      fprintf fmt "this may be due to a bug.@.";
      exit 1
    with
    | SAT.Unsat _  -> ()
    | (SAT.Sat _ | SAT.I_dont_know _) as e -> raise e


  let unused_context name context =
    match context with
    | None -> false
    | Some s -> not (Util.SS.mem name s)

  let mk_root_dep f_name =
    if Options.unsat_core () then Ex.singleton (Ex.RootDep f_name)
    else Ex.empty

  let process_decl print_status used_context ((env, consistent, dep) as acc) d =
    try
      match d.st_decl with
      | Assume(n, f, mf) ->
        let is_hyp = try (Char.equal '@' n.[0]) with _ -> false in
        if not is_hyp && unused_context n used_context then
          acc
        else
          let dep = if is_hyp then Ex.empty else mk_root_dep n in
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
          let dep = mk_root_dep name in
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
        if debug_unsat_core () then check_produced_unsat_core dep;
        if save_used_context () then output_used_context n dep;
        print_status (Unsat (d, dep)) (Steps.get_steps ());
        env, false, dep

      | ThAssume ({ Expr.ax_name; _ } as th_elt) ->
        if unused_context ax_name used_context then
          acc
        else
        if consistent then
          let dep = mk_root_dep ax_name in
          let env = SAT.assume_th_elt env th_elt dep in
          env, consistent, dep
        else env, consistent, dep

    with
    | SAT.Sat t ->
      print_status (Sat (d,t)) (Steps.get_steps ());
      if model () then SAT.print_model ~header:true std_formatter t;
      env , consistent, dep
    | SAT.Unsat dep' ->
      let dep = Ex.union dep dep' in
      if debug_unsat_core () then check_produced_unsat_core dep;
      print_status (Inconsistent d) (Steps.get_steps ());
      env , false, dep
    | SAT.I_dont_know t ->
      print_status (Unknown (d, t)) (Steps.get_steps ());
      if model () then SAT.print_model ~header:true std_formatter t;
      env , consistent, dep
    | Util.Timeout as e ->
      print_status (Timeout (Some d)) (Steps.get_steps ());
      raise e

  let goal_name d =
    match d.st_decl with
    | Query(n,_,_) -> sprintf " (goal %s)" n
    | _ -> ""

  let print_status_output_smtlib status steps =
    let time = Time.value() in
    match status with
    | Unsat (d, dep) ->
      let loc = d.st_loc in
      if Options.answers_with_locs () then
        eprintf "; %aValid (%2.4f) (%d steps)%s@."
          Loc.report loc time steps (goal_name d);
      printf "unsat@.";
      if unsat_core() && not (debug_unsat_core()) && not (save_used_context())
      then
        printf "(\n%a)@." (Ex.print_unsat_core ~tab:true) dep


    | Inconsistent _ ->
      ()
      (*
      let loc = d.st_loc in
      if Options.verbose () && Options.answers_with_locs () then
        eprintf "; %aInconsistent assumption@." report_loc loc
*)

    | Unknown (d, _) ->
      let loc = d.st_loc in
      if Options.answers_with_locs () then
        eprintf "; %aI don't know (%2.4f) (%d steps)%s@."
          Loc.report loc time steps (goal_name d);
      printf "unknown@."

    | Sat (d, _) ->
      let loc = d.st_loc in
      if Options.answers_with_locs () then
        eprintf "; %aInvalid (%2.4f) (%d steps)%s@."
          Loc.report loc time steps (goal_name d);
      printf "sat@."

    | Timeout (Some d) ->
      let loc = d.st_loc in
      if Options.answers_with_locs () then
        eprintf "; %aTimeout (%2.4f) (%d steps)%s@."
          Loc.report loc time steps (goal_name d);
      printf "timeout@."

    | Timeout None ->
      if Options.answers_with_locs () then
        eprintf "; %aTimeout (%2.4f) (%d steps)@."
          Loc.report Loc.dummy time steps;
      printf "timeout@."

    | Preprocess ->
      if Options.answers_with_locs () then
        eprintf "; %aPreprocessing (%2.4f) (%d steps)@."
          Loc.report Loc.dummy time steps


  let print_status_valid_mode status steps =
    let time = Time.value() in
    let report_loc fmt loc =
      if js_mode () then fprintf fmt "# [answer] "
      else if Options.answers_with_locs () then Loc.report fmt loc
    in
    match status with
    | Unsat (d, dep) ->
      let loc = d.st_loc in
      printf "%aValid (%2.4f) (%d steps)%s@."
        report_loc loc time steps (goal_name d);
      if unsat_core() && not (debug_unsat_core()) && not (save_used_context())
      then
        printf "unsat-core:\n%a@." (Ex.print_unsat_core ~tab:true) dep

    | Inconsistent d ->
      let loc = d.st_loc in
      if Options.verbose () then
        eprintf "%aInconsistent assumption@." report_loc loc

    | Sat (d, _) ->
      let loc = d.st_loc in
      printf "%aInvalid (%2.4f) (%d steps)%s@."
        report_loc loc time steps (goal_name d)

    | Unknown (d, _) ->
      let loc = d.st_loc in
      printf "%aI don't know (%2.4f) (%d steps)%s@."
        report_loc loc time steps (goal_name d)

    | Timeout (Some d) ->
      let loc = d.st_loc in
      printf "%aTimeout (%2.4f) (%d steps)%s@."
        report_loc loc time steps (goal_name d);

    | Timeout None ->
      printf "%aTimeout (%2.4f) (%d steps)@."
        report_loc Loc.dummy time steps;

    | Preprocess ->
      printf "%aPreprocessing (%2.4f) (%d steps)@."
        report_loc Loc.dummy time steps

  let print_status status steps =
    if Options.output_smtlib () then print_status_output_smtlib status steps
    else if Options.output_native () then print_status_valid_mode status steps
    else assert false           (* will be useful for szs *)

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
    if Options.replay_used_context () then
      let uc_f =
        sprintf "%s.%s.used" (Options.get_used_context_file ()) goal_name
      in
      if Sys.file_exists uc_f then init_with_replay_used None uc_f
      else
        begin
          fprintf fmt
            "File %s not found! Option -replay-used will be ignored@." uc_f;
          None
        end
    else
      None

  let init_all_used_context () =
    if Options.replay_all_used_context () then
      let dir = Filename.dirname (Options.get_used_context_file ()) in
      Array.fold_left
        (fun acc f ->
           let f = sprintf "%s/%s" dir f in
           if (Filename.check_suffix f ".used") then init_with_replay_used acc f
           else acc
        ) None (Sys.readdir dir)
    else None

  let choose_used_context all_ctxt ~goal_name =
    if Options.replay_all_used_context () then all_ctxt
    else init_used_context ~goal_name

end
