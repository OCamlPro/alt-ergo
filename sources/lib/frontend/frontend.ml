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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Typed
open Commands
open Format
open Options


module type S = sig

  type sat_env

  type output = Unsat of Explanation.t | Inconsistent
	        | Sat of sat_env | Unknown of sat_env

  val process_decl:
    (Commands.sat_tdecl -> output -> int64 -> unit) ->
    sat_env * bool * Explanation.t -> Commands.sat_tdecl ->
    sat_env * bool * Explanation.t

  val typecheck_file :
    Parsed.file ->
    ((int tdecl, int) annoted * Typechecker.env) list list

  val print_status : Commands.sat_tdecl -> output -> int64 -> unit
end

module Make(SAT : Sat_solver_sig.S) : S with type sat_env = SAT.t = struct

  type sat_env = SAT.t

  type output = Unsat of Explanation.t | Inconsistent
	        | Sat of sat_env | Unknown of sat_env

  let check_produced_proof dep =
    if verbose () then
      fprintf fmt "checking the proof:\n-------------------\n%a@."
        Explanation.print_proof dep;

    try
      let pb = Formula.Set.elements (Explanation.formulas_of dep) in
      let env =
        List.fold_left
          (fun env f ->
            SAT.assume env
	      {Formula.f=f;
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
          ) (SAT.empty ()) pb
      in
      ignore (SAT.unsat
                env
    	        {Formula.f=Formula.vrai;
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
      fprintf fmt "Checking produced proof failed!@.";
      fprintf fmt "this may be due to a bug.@.";
      exit 1
    with
      | SAT.Unsat _  -> ()
      | (SAT.Sat _ | SAT.I_dont_know _) as e -> raise e


  let do_save_used_context env dep =
    if not (Options.js_mode ()) then
      let used, unused = SAT.retrieve_used_context env dep in
      let f = Options.get_used_context_file () in
      let cout = open_out f in
      List.iter (fun f ->
        match Formula.view f with
        | Formula.Lemma {Formula.name=name} ->
          output_string cout (sprintf "%s\n" name)
        | _ -> assert false
      ) used;
      close_out cout

  let process_decl print_status (env, consistent, dep) d =
    try
      match d.st_decl with
        | Assume(n, f, mf) ->
          let hdist =
            try if Char.equal '@' n.[0] then 0 else -1 with _ -> -1
          in
          if consistent then
	    SAT.assume env
	      {Formula.f=f;
               origin_name = n;
               gdist = -1;
               hdist = hdist;
               trigger_depth = max_int;
               nb_reductions = 0;
               age=0;
               lem=None;
	       mf=mf;
               gf=false;
               from_terms = [];
               theory_elim = true;
              },
	    consistent, dep
          else env, consistent, dep
        | PredDef (f, name) ->
	  SAT.pred_def env f name d.st_loc, consistent, dep

        | RwtDef r -> assert false

        | Query(n, f, lits, sort) ->
	  let dep =
	    if consistent then
	      let dep' = SAT.unsat env
	        {Formula.f=f;
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
	      Explanation.union dep' dep
	    else dep
          in
          if debug_proof () then check_produced_proof dep;
          if save_used_context () then do_save_used_context env dep;
	  print_status d (Unsat dep) (SAT.get_steps ());
	  env, consistent, dep

      | ThAssume th_elt ->
        if consistent then
	  let env = SAT.assume_th_elt env th_elt in
	  env, consistent, dep
        else env, consistent, dep

    with
      | SAT.Sat t ->
        print_status d (Sat t) (SAT.get_steps ());
        if model () then SAT.print_model ~header:true std_formatter t;
        env , consistent, dep
      | SAT.Unsat dep' ->
        let dep = Explanation.union dep dep' in
        if debug_proof () then check_produced_proof dep;
        print_status d Inconsistent (SAT.get_steps ());
        env , false, dep
      | SAT.I_dont_know t ->
        print_status d (Unknown t) (SAT.get_steps ());
        if model () then SAT.print_model ~header:true std_formatter t;
        env , consistent, dep

  let typecheck_file (pfile : Parsed.file) =
      try
        let ltd, typ_env = Typechecker.file false Typechecker.empty_env pfile in
        let d = Typechecker.split_goals ltd in
        if type_only () then exit 0;
        d
      with
      | Errors.Error(e,l) ->
        Loc.report err_formatter l;
        eprintf "typing error: %a\n@." Errors.report e;
        exit 1

  let print_status d status steps =
    let time = Time.value() in
    let loc = d.st_loc in
    match status with
    | Unsat dep ->
      if Options.smt2_output () then printf "unsat@."
      else
        if js_mode () then
          printf "# [answer] Valid (%2.4f seconds) (%Ld steps)@." time steps
        else begin
          printf "%aValid (%2.4f) (%Ld steps)@." Loc.report loc time steps;
          if proof () && not (debug_proof ()) && not (save_used_context ()) then
            printf "Proof:\n%a@." Explanation.print_proof dep
        end

    | Inconsistent ->
      ()
      (*
      if js_mode () then
        printf "# [message] Inconsistent assumption \n@."
      else
        eprintf "%aInconsistent assumption@." Loc.report loc;
      *)

    | Unknown t | Sat t ->
      if Options.smt2_output () then printf "unknown@."
      else
        if js_mode () then
          printf "# [answer] unknown (%2.4f seconds) (%Ld steps)@." time steps
        else
          printf "%aI don't know (%2.4f) (%Ld steps)@." Loc.report loc time steps

end
