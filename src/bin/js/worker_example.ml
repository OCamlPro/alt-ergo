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

module Html = Dom_html

let document = Html.window##.document

(* Example of the file to prove *)
let file = ref "(set-logic ALL)\n(check-sat)"

(* This is the extension needed for the parser and corresponding to the input
   file format*)
let extension = ref ".psmt2"

(* Timeout *)
let timeout = ref 100.

(* Function that run the worker. *)
let exec worker file options =
  (* create a cancelable promise that can be cancel in case of timeout *)
  let t, resolver = Lwt.task () in
  (* Set the behaviour of the worker when Lwt send an on_cancel input *)
  Lwt.on_cancel t (fun () -> worker##terminate);
  (* Get the messages returned from the worker and return them *)
  worker##.onmessage :=
    (Js_of_ocaml.Dom_html.handler (fun msg ->
         let res = msg##.data in
         Lwt.wakeup resolver res;
         Js_of_ocaml.Js._true));
  (* Start the worker with the correspondin input, here file_options *)
  worker##postMessage (file,options);
  t

(* Create the web worker and launch 2 threads.
   The first one for the timeout,
   the second on for the call to Alt-Ergo through his web worker *)
let solve () =
  let options =
    {(Worker_interface.init_options ()) with
     input_format = None;
     debug = Some false;
     verbose = Some false;
     answers_with_loc = Some false;
     sat_solver = Some Worker_interface.CDCL_Tableaux;
     unsat_core = Some false;
    } in

  let worker = Worker.create "./alt-ergo-worker.js" in

  (Lwt.pick [
      (let%lwt () = Lwt_js.sleep !timeout in
       Lwt.return {(Worker_interface.init_results ()) with
                   diagnostic = Some ["Timeout"]});
      (
        let file = String.split_on_char '\n' !file in
        let json_file =
          Worker_interface.file_to_json
            (Some ("dummy" ^ !extension)) (Some 42) file
        in
        Console.console##log json_file;
        let json_options = Worker_interface.options_to_json options in
        Console.console##log json_options;
        let%lwt results = exec worker json_file json_options in
        Console.console##log results;
        let res = Worker_interface.results_from_json results in
        Lwt.return res
      )
    ]
  )

let string_input f area_name area =
  let res = document##createDocumentFragment in
  Dom.appendChild res (document##createTextNode (Js.string area_name));
  Dom.appendChild res (Html.createBr document);
  let input = f document in
  input##.value := Js.string !area;
  input##.onchange :=
    Html.handler (fun _ ->
        (try area := Js.to_string input##.value
         with Invalid_argument _ -> ());
        input##.value := Js.string !area;
        Js._false);
  Dom.appendChild res input;
  Dom.appendChild res (Html.createBr document);
  res

let float_input name value =
  let res = document##createDocumentFragment in
  Dom.appendChild res (document##createTextNode (Js.string name));
  Dom.appendChild res (Html.createBr document);
  let input = Html.createInput document in
  input##.value := Js.string (string_of_float !value);
  input##.onchange :=
    Html.handler (fun _ ->
        (try value := float_of_string (Js.to_string input##.value)
         with Invalid_argument _ -> ());
        input##.value := Js.string (string_of_float !value);
        Js._false);
  Dom.appendChild res input;
  Dom.appendChild res (Html.createBr document);
  res

let button name callback =
  let res = document##createDocumentFragment in
  let input = Html.createInput ~_type:(Js.string "submit") document in
  input##.value := Js.string name;
  input##.onclick := Html.handler callback;
  Dom.appendChild res input;
  res

let process_results = function
  | Some r ->
    Some (String.concat "" r)
  | None -> None

let regular =
  let div = Html.createDiv document in
  div##.className := Js.string "regular";
  div

let print_regular v =
  match v with
  | Some s ->
    regular##.innerText := Js.string s
  | None -> ()

let diagnostic =
  let div = Html.createDiv document in
  div##.className := Js.string "diagnostic";
  div

let statistics = document##createTextNode (Js.string "")
let print_statistics = function
  | None -> ()
  | Some l ->
    let stats = List.fold_left (fun acc (name,begin_pos,end_pos,nb,used) ->
        let used = match used with
          | Worker_interface.Used -> "Used"
          | Worker_interface.Unused -> "Unused"
          | Worker_interface.Unknown -> "_"
        in
        (Format.sprintf "%s \n %s (%d-%d) #%d: %s"
           acc name begin_pos end_pos nb used)
      ) "" l in
    statistics##.data := Js.string stats

let print_diagnostic v =
  match v with
  | Some s ->
    diagnostic##.innerText := Js.string s
  | None -> ()

let onload _ =
  let main = Js.Opt.get (document##getElementById (Js.string "main"))
      (fun () -> assert false) in
  Dom.appendChild main
    (string_input Html.createTextarea "Input file to solve" file);
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild main (string_input Html.createInput "Extension" extension);
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild main (float_input "Timeout" timeout);
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild
    main
    (button "Ask Alt-Ergo" (fun _ ->
         let div = Html.createDiv document in
         Dom.appendChild main div;
         Lwt_js_events.async (fun () ->
             print_regular (Some "Solving");
             print_diagnostic (Some "");
             let%lwt res = solve () in
             print_regular (process_results res.regular);
             print_diagnostic (process_results res.diagnostic);
             print_statistics res.statistics;
             Lwt.return_unit);
         Js._false));
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild main regular;
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild main diagnostic;
  Dom.appendChild main (Html.createBr document);
  Dom.appendChild main (Html.createBr document);
  Js._false

let _ = Html.window##.onload := Html.handler onload
