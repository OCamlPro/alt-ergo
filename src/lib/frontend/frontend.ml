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

open Commands
open Format
open Options

module E = Expr
module Ex = Explanation
module type S = sig

  type sat_env

  type used_context

  type res = [
    | `Sat of sat_env
    | `Unknown of sat_env
    | `Unsat
  ]

  type t = sat_env * res * Ex.t

  type status =
    | Unsat of Commands.sat_tdecl * Ex.t
    | Inconsistent of Commands.sat_tdecl
    | Sat of Commands.sat_tdecl * sat_env
    | Unknown of Commands.sat_tdecl * sat_env
    | Timeout of Commands.sat_tdecl option
    | Preprocess

  type 'input process_decl_base =
    used_context ->
    (res * Ex.t) Stack.t ->
    Loc.t ->
    t ->
    'input ->
    t

  val push : int process_decl_base

  val pop : int process_decl_base

  val assume : (string * E.t * bool) process_decl_base

  val pred_def : (E.t * string) process_decl_base

  val query : (string * E.t * Ty.goal_sort) process_decl_base

  val assume_th_elt : E.th_elt process_decl_base

  val process_decl:
    (status -> int -> unit) ->
    used_context ->
    (res * Ex.t) Stack.t ->
    sat_env * res * Ex.t ->
    Commands.sat_tdecl ->
    sat_env * res * Ex.t

  val print_status : status -> int -> unit

  val init_all_used_context : unit -> used_context
  val choose_used_context : used_context -> goal_name:string -> used_context

end

module Make(SAT : Sat_solver_sig.S) : S with type sat_env = SAT.t = struct

  type sat_env = SAT.t
  type used_context = Util.SS.t option

  type res = [
    | `Sat of sat_env
    | `Unknown of sat_env
    | `Unsat
  ]

  type t = sat_env * res * Ex.t

  type status =
    | Unsat of Commands.sat_tdecl * Ex.t
    | Inconsistent of Commands.sat_tdecl
    | Sat of Commands.sat_tdecl * sat_env
    | Unknown of Commands.sat_tdecl * sat_env
    | Timeout of Commands.sat_tdecl option
    | Preprocess

  exception SAT of SAT.t
  exception UNSAT of Explanation.t
  exception I_DONT_KNOW of SAT.t

  (** Returns the environment if the API call was successful
      (i.e., returned 'Done'). Otherwise, raises an exceptio*)
  let process_sat_res = function
    | `Sat t -> raise (SAT t)
    | `Unsat e -> raise (UNSAT e)
    | `Unknown t -> raise (I_DONT_KNOW t)

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
    let pb = E.Set.elements (Ex.formulas_of dep) in
    let env =
      List.fold_left
        (fun env f ->
           process_sat_res @@
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
    match
      SAT.unsat
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
        }
    with
    | `Unsat _ -> Errors.run_error Errors.Failed_check_unsat_core
    | `Sat t -> raise (SAT t)
    | `Unknown t -> raise (I_DONT_KNOW t)

  let unused_context name context =
    match context with
    | None -> false
    | Some s -> not (Util.SS.mem name s)

  let mk_root_dep name f loc =
    if Options.get_unsat_core () then Ex.singleton (Ex.RootDep {name;f;loc})
    else Ex.empty

  type 'input process_decl_base =
    used_context ->
    (res * Explanation.t) Stack.t ->
    Loc.t ->
    t ->
    'input ->
    t

  let[@inline] push : int process_decl_base =
    fun
      _used_context
      consistent_dep_stack
      _loc
      (env, consistent, dep)
      n ->
      Util.loop ~f:(fun _n env () -> Stack.push env consistent_dep_stack)
        ~max:n ~elt:(consistent, dep) ~init:();
      SAT.push env n, consistent, dep

  let[@inline] pop : int process_decl_base =
    fun
      _used_context
      consistent_dep_stack
      _loc
      (env, consistent, dep)
      n ->
      let consistent, dep =
        Util.loop ~f:(fun _n () _env -> Stack.pop consistent_dep_stack)
          ~max:n ~elt:() ~init:(consistent, dep)
      in
      SAT.pop env n, consistent, dep

  let[@inline] assume : (string * E.t * bool) process_decl_base =
    fun
      used_context
      _consistent_dep_stack
      loc
      ((env, consistent, _dep) as acc)
      (n, f, mf) : (sat_env * res * Ex.t) ->
      let is_hyp = try (Char.equal '@' n.[0]) with _ -> false in
      if not is_hyp && unused_context n used_context then
        acc
      else
        let dep = if is_hyp then Ex.empty else mk_root_dep n f loc in
        begin
          match consistent with
          | `Sat _ | `Unknown _ ->
            begin
              match
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
                  } dep
              with
              | `Unknown new_env -> new_env, consistent, dep
              | `Unsat dep' ->
                let dep = Ex.union dep dep' in
                if get_debug_unsat_core () then check_produced_unsat_core dep;
                env, `Unsat, dep
            end
          | `Unsat ->
            env, consistent, dep
        end

  let[@inline] pred_def : (Expr.t * string) process_decl_base =
    fun
      used_context
      _consistent_dep_stack
      loc
      ((env, consistent, _dep) as acc)
      (f, name) ->
      if unused_context name used_context then acc
      else
        let dep = mk_root_dep name f loc in
        SAT.pred_def env f name dep loc,
        consistent,
        dep

  let[@inline] query : (string * Expr.t * Ty.goal_sort) process_decl_base =
    fun
      _used_context
      _consistent_dep_stack
      _loc
      ((env, consistent, dep) as acc)
      (n, f, sort) ->
      let (_env, consistent, dep) as res =
        match consistent with
        | `Sat _ | `Unknown _ ->
          begin
            match
              SAT.unsat env
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
            with
            | `Unsat dep' ->
              let dep = Ex.union dep dep' in
              if get_debug_unsat_core () then check_produced_unsat_core dep;
              env, `Unsat, dep
            | `Unknown t -> env, `Unknown t, dep
            | `Sat t -> env, `Sat t, dep
          end
        | `Unsat -> acc
      in
      match consistent with
      | `Unsat ->
        if get_debug_unsat_core () then check_produced_unsat_core dep;
        if get_save_used_context () then output_used_context n dep;
        res
      | (`Sat _ | `Unknown _) -> res

  let[@inline] assume_th_elt : Expr.th_elt process_decl_base =
    fun
      used_context
      _consistent_dep_stack
      loc
      ((env, consistent, dep) as acc)
      ({ Expr.ax_name; Expr.ax_form ; _ } as th_elt) ->
      if unused_context ax_name used_context then
        acc
      else
        match consistent with
        | `Sat _ | `Unknown _ ->
          begin
            let dep = mk_root_dep ax_name ax_form loc in
            let env = SAT.assume_th_elt env th_elt dep in
            env, consistent, dep
          end
        | `Unsat ->
          env, consistent, dep

  let process_decl
      print_status
      used_context
      consistent_dep_stack
      acc
      d =
    try
      match d.st_decl with
      | Push n ->
        push used_context consistent_dep_stack d.st_loc acc n
      | Pop n ->
        pop used_context consistent_dep_stack d.st_loc acc n
      | Assume(n, f, mf) ->
        assume
          used_context
          consistent_dep_stack
          d.st_loc
          acc
          (n, f, mf)
      | PredDef (f, name) ->
        pred_def
          used_context
          consistent_dep_stack
          d.st_loc
          acc
          (f, name)
      | RwtDef _ -> assert false
      | Query(n, f, sort) ->
        begin
          let (env, consistent, dep) as res =
            query
              used_context
              consistent_dep_stack
              d.st_loc
              acc
              (n, f, sort)
          in
          match consistent with
          | `Unsat ->
            print_status (Unsat (d, dep)) (Steps.get_steps ());
            (env, `Unsat, dep)
          | `Sat t ->
            (* This case should mainly occur when a query has a non-unsat
               result, so we want to print the status in this case. *)
            print_status (Sat (d,t)) (Steps.get_steps ());
            res
          | `Unknown t ->
            (* In this case, it's not clear whether we want to print the status.
               Instead, it'd be better to accumulate in `consistent` a 3-case
               adt and not a simple bool. *)
            print_status (Unknown (d, t)) (Steps.get_steps ());
            (* if get_model () then
                 SAT.print_model ~header:true (get_fmt_mdl ()) t; *)
            res
        end
      | ThAssume th_elt ->
        assume_th_elt
          used_context
          consistent_dep_stack
          d.st_loc
          acc
          th_elt
    with
    | Util.Timeout as e ->
      (* In this case, we obviously want to print the status,
         since we exit right after  *)
      print_status (Timeout (Some d)) (Steps.get_steps ());
      raise e

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
        Printer.print_fmt (Options.Output.get_fmt_usc ())
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
