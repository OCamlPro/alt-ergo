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

let main ~worker_id input =
  let buf_regular = create_buffer () in
  Options.Output.set_regular (snd buf_regular);
  let buf_diagnostic = create_buffer () in
  Options.Output.set_diagnostic (snd buf_diagnostic);
  let return_answer ?statistics status =
    let regular = check_buffer_content buf_regular in
    let diagnostic = check_buffer_content buf_diagnostic in
    Worker_interface.{ worker_id; status; regular; diagnostic; statistics }
  in
  let return_error fmt = Format.kasprintf (fun s -> return_answer (Error s)) fmt in

  let tbl = Hashtbl.create 53 in
  (* Aux function used to record axioms used in instantiations *)
  let selector_inst orig =
    let id = Expr.uid orig in
    begin
      try incr (snd (Hashtbl.find tbl id))
      with Not_found -> Hashtbl.add tbl id (orig, ref 1)
    end;
    true
  in
  let unsat_core = ref [] in

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
              let b,e = Loc.lexing_positions loc in
              let used =
                if Options.get_unsat_core () then Worker_interface.Unused
                else Worker_interface.Unknown in
              (name,b.Lexing.pos_lnum,e.Lexing.pos_lnum,!nb,used) :: acc
            | _ -> acc
          end
        | Some r ->
          let b,e = Loc.lexing_positions r.loc in
          (r.name,b.Lexing.pos_lnum,e.Lexing.pos_lnum,
           !nb,Worker_interface.Used)
          :: acc
      ) tbl []
  in

  try
    let returned_status = ref (Worker_interface.Unknown 0) in
    let print_status status n =
      returned_status :=
        begin match status with
          | Frontend.Unsat _ -> Worker_interface.Unsat n
          | Inconsistent _ -> Worker_interface.Inconsistent n
          | Sat _ -> Worker_interface.Sat n
          | Unknown _ -> Worker_interface.Unknown n
          | Timeout _ -> Worker_interface.LimitReached "timeout"
        end;
      Frontend.print_status status n
    in
    Solving_loop.process_source ~selector_inst ~print_status input;
    let statistics = check_context_content @@ compute_statistics () in
    return_answer ?statistics !returned_status
  with
  | Assert_failure (s, l, p) ->
    return_error "Assertion failure: %s %d %d" s l p
  | Errors.Error e ->
    return_error "%a" Errors.report e
  | exn ->
    let exn = Printexc.to_string exn in
    if Printexc.backtrace_status () then
      let bt = Printexc.(raw_backtrace_to_string @@ get_raw_backtrace ()) in
      return_error "Uncaught exception %s:@ %s" exn bt
    else
      return_error "Uncaught exception %s" exn

(** Worker initialisation
    Run Alt-ergo with the input file (string)
    and the corresponding set of options
    Return a couple of list for status (one per goal) and errors *)
let () =
  Worker.set_onmessage (fun (json_file, json_options) ->
      Lwt_js_events.async (fun () ->
          let filename, worker_id, content =
            Worker_interface.file_from_json json_file
          in
          let options = Worker_interface.options_from_json json_options in
          Options_interface.set_options options;
          let input =
            let content = String.concat "\n" content in
            let filename = Option.value ~default:"<input>" filename in
            `Raw (filename, content)
          in
          let results = main ~worker_id input in
          Worker.post_message (Worker_interface.results_to_json results);
          Lwt.return ()))
