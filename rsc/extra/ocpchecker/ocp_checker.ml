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

let remove_trailing_whitespaces line =
  let len = String.length line in
  let new_len = ref len in
  let loop = ref (!new_len > 0) in
  while !loop do
    let c = line.[!new_len - 1] in
    if c = ' ' || c = '\t' || c = '\r' then
      begin
        decr new_len;
        loop := !new_len > 0
      end
    else loop := false
  done;
  if !new_len <> len then Some (String.sub line 0 !new_len)
  else None

let print_err file_opt =
  Option.iter (Format.eprintf "File %s: ") file_opt;
  Format.eprintf

let check_buffer file_opt cin =
  let spacesRemoved = ref false in
  let longLines = ref false in
  let lines = Queue.create () in
  let cpt = ref 0 in
  try
    while true do
      incr cpt;
      let line = input_line cin in
      let line =
        match remove_trailing_whitespaces line with
        | None       -> Queue.push line  lines; line
        | Some line2 -> Queue.push line2 lines; spacesRemoved := true; line2
      in
      if String.length line > 80 then begin
        print_err file_opt "line %d too long@." !cpt;
        longLines := true;
      end
    done;
    assert false
  with End_of_file -> lines, !spacesRemoved, !longLines

let update_file cout lines =
  Queue.iter (fun line ->
      Stdlib.output_string cout line;
      Stdlib.output_string cout "\n"
    )lines;
  Stdlib.flush cout;
  close_out cout

let check_file file_opt =
  let cin =
    match file_opt with
    | None -> stdin
    | Some file ->
      try open_in file
      with e ->
        Format.eprintf "Error while opening (in) file: %s@.%s@."
          file (Printexc.to_string e);
        exit 2
  in
  let lines, spacesRemoved, longLines = check_buffer file_opt cin in
  close_in cin;
  if spacesRemoved || Option.is_none file_opt then begin
    let cout =
      match file_opt with
      | None -> stdout
      | Some file ->
        try open_out file
        with e ->
          Format.eprintf "Error while opening (out) file: %s@.%s@."
            file (Printexc.to_string e);
          exit 2
    in
    update_file cout lines
  end;
  if spacesRemoved then exit 10;
  if longLines then exit 11


let () =
  match Array.length Sys.argv with
  | 0 | 1 ->
    check_file None
  | 2 ->
    check_file @@ Some Sys.argv.(1)

  | _ ->
    Format.eprintf "%s: Too many arguments!@." Sys.argv.(0); exit 4
