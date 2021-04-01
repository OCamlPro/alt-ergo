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

(* If the buffer is not empty split the string in strings at each newline *)
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

let main worker_id content =
  try
    (* Create buffer for each formatter
       The content of this buffers are then retrieved and send as results *)
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
          | FE.Unsat _ -> Worker_interface.Unsat n
          | FE.Inconsistent _ -> Worker_interface.Inconsistent n
          | FE.Sat _ -> Worker_interface.Sat n
          | FE.Unknown _ -> Worker_interface.Unknown n
          | FE.Timeout _ -> Worker_interface.LimitReached "timeout"
          | FE.Preprocess -> Worker_interface.Unknown n
        end;
      FE.print_status status n
    in

    let solve all_context (cnf, goal_name) =
      let used_context = FE.choose_used_context all_context ~goal_name in
      let consistent_dep_stack = Stack.create () in
      SAT.reset_refs ();
      let _,_,dep =
        List.fold_left
          (FE.process_decl
             get_status_and_print used_context consistent_dep_stack)
          (SAT.empty_with_inst add_inst, true, Explanation.empty) cnf in

      if Options.get_unsat_core () then begin
        unsat_core := Explanation.get_unsat_core dep;
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
        I.parse_file ~content ~format:None
      with
      | Parsing.Parse_error ->
        Printer.print_err "%a" Errors.report
          (Syntax_error ((Lexing.dummy_pos,Lexing.dummy_pos),""));
        raise Exit
      | Errors.Error e ->
        begin match e with
          | Errors.Run_error r -> begin
              match r with
              | Steps_limit _ ->
                returned_status :=
                  Worker_interface.LimitReached "Steps limit"
              | _ -> returned_status := Worker_interface.Error "Run error"
            end
          | _ -> returned_status := Worker_interface.Error "Error"
        end;
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
      Worker_interface.results = check_buffer_content buf_std;
      Worker_interface.errors = check_buffer_content buf_err;
      Worker_interface.warnings = check_buffer_content buf_wrn;
      Worker_interface.debugs = check_buffer_content buf_dbg;
      Worker_interface.statistics =
        check_context_content (compute_statistics ());
      Worker_interface.model = check_buffer_content buf_mdl;
      Worker_interface.unsat_core = check_buffer_content buf_usc;
    }

  with
  | Assert_failure (s,l,p) ->
    let res = Worker_interface.init_results () in
    { res with
      Worker_interface.worker_id = worker_id;
      Worker_interface.status = Error "Assertion failure";
      Worker_interface.errors =
        Some [Format.sprintf "assertion failed: %s line %d char %d" s l p];
    }
  | Errors.Error e ->
    let res = Worker_interface.init_results () in
    { res with
      Worker_interface.worker_id = worker_id;
      Worker_interface.status = Error "";
      Worker_interface.errors =
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
