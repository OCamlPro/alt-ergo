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

open Js_of_ocaml
open Js_of_ocaml_lwt
open Alt_ergo_common
open AltErgoLib

(* Internal state while iterating over input statements *)
type 'a state = {
  env : 'a;
  ctx   : Commands.sat_tdecl list;
  local : Commands.sat_tdecl list;
  global : Commands.sat_tdecl list;
}

(* If the buffer is not empty split the string in strings at each newline *)
let check_buffer_content (buf, output) =
  Format.pp_print_flush (Options.Output.to_formatter output) ();
  let buf_cont = Buffer.contents buf in
  if String.equal buf_cont "" then
    None
  else
    let buf = String.split_on_char '\n' buf_cont in
    Some buf

let check_context_content c =
  match c with
  | [] -> None
  | _ -> Some c

let create_buffer () =
  let buf = Buffer.create 10 in
  let output =
    Format.formatter_of_buffer buf
    |> Options.Output.of_formatter
  in
  buf, output

let main worker_id content =
  try
    (* Create buffer for each formatter
       The content of this buffers are then retrieved and send as results *)
    let buf_regular = create_buffer () in
    Options.Output.set_regular (snd buf_regular);
    let buf_diagnostic = create_buffer () in
    Options.Output.set_diagnostic (snd buf_diagnostic);

    (* Status updated regarding if AE succed or failed
       (error or steplimit reached) *)
    let returned_status = ref (Worker_interface.Unknown 0) in

    (* let context = ref ([],[]) in *)
    let unsat_core = ref [] in
    let tbl = Hashtbl.create 53 in


    (* Initialisation *)
    Input_frontend.register_legacy ();

    let module SatCont =
      (val (Sat_solver.get_current ()) : Sat_solver_sig.SatContainer) in

    let module TH =
      (val
        (if Options.get_no_theory() then (module Theory.Main_Empty : Theory.S)
         else (module Theory.Main_Default : Theory.S)) : Theory.S ) in

    let module SAT = SatCont.Make(TH) in

    let module FE = Frontend.Make (SAT) in

    (* Aux function used to record axioms used in instantiations *)
    let add_inst orig =
      let id = Expr.uid orig in
      begin
        try incr (snd (Hashtbl.find tbl id))
        with Not_found -> Hashtbl.add tbl id (orig, ref 1)
      end;
      true
    in

    let get_status_and_print status n =
      returned_status :=
        begin match status with
          | Frontend.Unsat _ -> Worker_interface.Unsat n
          | Inconsistent _ -> Worker_interface.Inconsistent n
          | Sat _ -> Worker_interface.Sat n
          | Unknown _ -> Worker_interface.Unknown n
          | Timeout _ -> Worker_interface.LimitReached "timeout"
          | Preprocess -> Worker_interface.Unknown n
        end;
      Frontend.print_status status n
    in

    let solve all_context (cnf, goal_name) =
      let used_context = Frontend.choose_used_context all_context ~goal_name in
      SAT.reset_refs ();
      let sat_env = SAT.empty ~selector:add_inst () in
      let ftnd_env = FE.init_env ~sat_env used_context in
      List.iter
        (FE.process_decl ~hook_on_status:get_status_and_print ftnd_env)
        cnf;
      if Options.get_unsat_core () then begin
        unsat_core := Explanation.get_unsat_core ftnd_env.FE.expl;
      end;
      let () =
        match ftnd_env.FE.res with
        | `Sat | `Unknown ->
          begin
            if Options.(get_interpretation () && get_dump_models ()) then
              FE.print_model
                (Options.Output.get_fmt_models ())
                ftnd_env.sat_env;
          end
        | `Unsat -> ()
      in
      ()
    in

    let typed_loop all_context state td =
      match td.Typed.c with
      | Typed.TGoal (_, kind, name, _) ->
        let l = state.local @ state.global @ state.ctx in
        let cnf = List.rev @@ Cnf.make l td in
        let () = solve all_context (cnf, name) in
        begin match kind with
          | Ty.Check
          | Ty.Cut -> { state with local = []; }
          | Ty.Thm | Ty.Sat -> { state with global = []; local = []; }
        end
      | Typed.TAxiom (_, s, _, _) when Ty.is_global_hyp s ->
        let cnf = Cnf.make state.global td in
        { state with global = cnf; }
      | Typed.TAxiom (_, s, _, _) when Ty.is_local_hyp s ->
        let cnf = Cnf.make state.local td in
        { state with local = cnf; }
      | _ ->
        let cnf = Cnf.make state.ctx td in
        { state with ctx = cnf; }
    in

    let (module I : Input.S) = Input.find (Options.get_frontend ()) in
    let parsed () =
      try
        Options.Time.start ();
        I.parse_file ~content ~format:None
      with
      | Parsing.Parse_error ->
        Printer.print_err "%a" Errors.report
          (Syntax_error ((Lexing.dummy_pos,Lexing.dummy_pos),""));
        raise Exit
      | Errors.Error e ->
        begin match e with
          | Errors.Run_error _ ->
            returned_status := Worker_interface.Error "Run error"
          | _ -> returned_status := Worker_interface.Error "Error"
        end;
        Printer.print_err "%a" Errors.report e;
        raise Exit
    in
    let all_used_context = Frontend.init_all_used_context () in
    let assertion_stack = Stack.create () in
    let typing_loop state p =
      try
        let l, env = I.type_parsed state.env assertion_stack p in
        List.fold_left (typed_loop all_used_context) { state with env; } l
      with Errors.Error e ->
        Printer.print_err "%a" Errors.report e;
        raise Exit
    in

    let state = {
      env = I.empty_env;
      ctx = [];
      local = [];
      global = [];
    } in

    begin
      try let _ : _ state =
            Seq.fold_left typing_loop state (parsed ()) in ()
      with Exit -> () end;

    let compute_statistics () =
      let used =
        List.fold_left (fun acc ({Explanation.f;_} as r) ->
            Util.MI.add (Expr.uid f) r acc
          ) Util.MI.empty (!unsat_core) in
      Hashtbl.fold (fun id (f,nb) acc ->
          match Util.MI.find_opt id used with
          | None -> begin
              match Expr.form_view f with
              | Lemma {name=name;loc=loc;_} ->
                let b,e = loc in
                let used =
                  if Options.get_unsat_core () then Worker_interface.Unused
                  else Worker_interface.Unknown in
                (name,b.Lexing.pos_lnum,e.Lexing.pos_lnum,!nb,used) :: acc
              | _ -> acc
            end
          | Some r ->
            let b,e = r.loc in
            (r.name,b.Lexing.pos_lnum,e.Lexing.pos_lnum,
             !nb,Worker_interface.Used)
            :: acc
        ) tbl []
    in


    (* returns a records with compatible worker_interface fields *)
    {
      Worker_interface.worker_id = worker_id;
      Worker_interface.status = !returned_status;
      Worker_interface.regular = check_buffer_content buf_regular;
      Worker_interface.diagnostic = check_buffer_content buf_diagnostic;
      Worker_interface.statistics =
        check_context_content (compute_statistics ());
    }

  with
  | Assert_failure (s,l,p) ->
    let res = Worker_interface.init_results () in
    { res with
      Worker_interface.worker_id = worker_id;
      Worker_interface.status = Error "Assertion failure";
      Worker_interface.diagnostic =
        Some [Format.sprintf "assertion failed: %s line %d char %d" s l p];
    }
  | Errors.Error e ->
    let res = Worker_interface.init_results () in
    { res with
      Worker_interface.worker_id = worker_id;
      Worker_interface.status = Error "";
      Worker_interface.diagnostic =
        Some [Format.asprintf "%a" Errors.report e]
    }
  | _ ->
    let res = Worker_interface.init_results () in
    { res with
      Worker_interface.worker_id = worker_id;
      Worker_interface.status = Error "Unknown error";
    }

(** Worker initialisation
    Run Alt-ergo with the input file (string)
    and the corresponding set of options
    Return a couple of list for status (one per goal) and errors *)
let () =
  at_exit Options.Output.close_all;
  Worker.set_onmessage (fun (json_file,json_options) ->
      Lwt_js_events.async (fun () ->
          let filename,worker_id,filecontent =
            Worker_interface.file_from_json json_file in
          begin match filename with
            | Some fl -> Options.set_file_for_js fl
            | None -> Options.set_file_for_js ""
          end;
          let filecontent = String.concat "\n" filecontent in
          (* Format.eprintf
             "file content : @, %s @,@, end of file @." filecontent; *)

          (* Extract options and set them *)
          let options = Worker_interface.options_from_json json_options in
          Options_interface.set_options options;

          (* Run the worker on the input file (filecontent) *)
          let results = main worker_id filecontent in

          (* Convert results and returns them *)
          Worker.post_message (Worker_interface.results_to_json results);
          Lwt.return ();
        )
    )
