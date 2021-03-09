(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

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

let check_buffer_content b =
  let buf_cont = Buffer.contents b in
  if String.equal buf_cont "" then
    None
  else
    let buf = String.split_on_char '\n' buf_cont in
    Some buf

let check_context_content c =
  match c with
  | [] -> None
  | _ -> Some c

let main file =
  let buf_std = Buffer.create 10 in
  Options.set_fmt_std (Format.formatter_of_buffer buf_std);
  let buf_err = Buffer.create 10 in
  Options.set_fmt_err (Format.formatter_of_buffer buf_err);
  let buf_wrn = Buffer.create 10 in
  Options.set_fmt_wrn (Format.formatter_of_buffer buf_wrn);
  let buf_dbg = Buffer.create 10 in
  Options.set_fmt_dbg (Format.formatter_of_buffer buf_dbg);
  let buf_mdl = Buffer.create 10 in
  Options.set_fmt_mdl (Format.formatter_of_buffer buf_mdl);
  let buf_usc = Buffer.create 10 in
  Options.set_fmt_usc (Format.formatter_of_buffer buf_usc);

  let context = ref ([],[]) in
  let tbl = Hashtbl.create 53 in

  Input_frontend.register_legacy ();

  let module SatCont =
    (val (Sat_solver.get_current ()) : Sat_solver_sig.SatContainer) in

  let module TH =
    (val
      (if Options.get_no_theory() then (module Theory.Main_Empty : Theory.S)
       else (module Theory.Main_Default : Theory.S)) : Theory.S ) in

  let module SAT = SatCont.Make(TH) in

  let module FE = Frontend.Make (SAT) in

  let add_inst orig =
    let id = Expr.uid orig in
    begin
      try incr (snd (Hashtbl.find tbl id))
      with Not_found -> Hashtbl.add tbl id (orig, ref 1)
    end;
    true
  in

  let compute_used_context env dep =
    let compute_used_context_aux l =
      List.fold_left (fun acc f ->
          match Expr.form_view f with
          | Lemma {name=name;loc=loc;_} ->
            let b,e = loc in
            (Expr.uid f,name,b.Lexing.pos_lnum,e.Lexing.pos_lnum) :: acc
          | _ -> acc
        )[] l in
    let used,unused = SAT.retrieve_used_context env dep in
    (compute_used_context_aux used,compute_used_context_aux unused) in

  let solve all_context (cnf, goal_name) =
    let used_context = FE.choose_used_context all_context ~goal_name in
    let consistent_dep_stack = Stack.create () in
    SAT.reset_refs ();
    let env,_,dep =
      List.fold_left
        (FE.process_decl
           FE.print_status used_context consistent_dep_stack)
        (SAT.empty_with_inst add_inst, true, Explanation.empty) cnf in

    if Options.get_save_used_context () then begin
      (* Format.eprintf "Solve finished, print context@."; *)
      context := compute_used_context env dep;

      (* List.iter (fun (used,_,_) ->
          Format.eprintf "Used : %s@." used
         ) (fst !context); *)
    end;
  in

  let typed_loop all_context state td =
    match td.Typed.c with
    | Typed.TGoal (_, kind, name, _) ->
      let l = state.local @ state.global @ state.ctx in
      let cnf = List.rev @@ Cnf.make l td in
      let () = solve all_context (cnf, name) in
      begin match kind with
        | Typed.Check
        | Typed.Cut -> { state with local = []; }
        | _ -> { state with global = []; local = []; }
      end
    | Typed.TAxiom (_, s, _, _) when Typed.is_global_hyp s ->
      let cnf = Cnf.make state.global td in
      { state with global = cnf; }
    | Typed.TAxiom (_, s, _, _) when Typed.is_local_hyp s ->
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
      Options.set_is_gui false;
      I.parse_file ~file ~format:None
    with
    | Parsing.Parse_error ->
      Printer.print_err "%a" Errors.report
        (Syntax_error ((Lexing.dummy_pos,Lexing.dummy_pos),""));
      raise Exit
    | Errors.Error e ->
      Printer.print_err "%a" Errors.report e;
      raise Exit
  in
  let all_used_context = FE.init_all_used_context () in
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


  let compute_statistics (used,unused) =
    let aux stats l =
      List.fold_left (fun acc (id,name,pos_start,pos_end) ->
          match Hashtbl.find_opt tbl id with
          | Some (_f,nb) ->
             (name,pos_start,pos_end,!nb) :: acc
          | None ->
             (name,pos_start,pos_end,0) :: acc
        ) stats l in
    let used_stats = aux [] used in
    let stats = aux used_stats unused in
    List.rev stats
  in

  {
    Worker_interface.results = check_buffer_content buf_std;
    Worker_interface.errors = check_buffer_content buf_err;
    Worker_interface.warnings = check_buffer_content buf_wrn;
    Worker_interface.debugs = check_buffer_content buf_dbg;
    Worker_interface.statistics =
      check_context_content (compute_statistics (!context));
    Worker_interface.model = check_buffer_content buf_mdl;
    Worker_interface.unsat_core = check_buffer_content buf_usc;
  }



(** Worker initialisation
    Run Alt-ergo with the input file (string)
    and the corresponding set of options
    Return a couple of list for status (one per goal) and errors *)
let () =
  Worker.set_onmessage (fun (json_file,json_options) ->
      Lwt_js_events.async (fun () ->
          let filename,filecontent =
            Worker_interface.file_from_json json_file in
          begin match filename with
            | Some fl -> Options.set_file_for_js fl
            | None -> Options.set_file_for_js ""
          end;
          let filecontent = String.concat "\n" filecontent in
          (* Format.eprintf
             "file content : @, %s @,@, end of file @." filecontent; *)
          let options = Worker_interface.options_from_json json_options in
          Options_interface.set_options options;

          let results = main filecontent in
          Worker.post_message (Worker_interface.results_to_json results);
          (* Worker.post_message results; *)
          Lwt.return ();
        )
    )
