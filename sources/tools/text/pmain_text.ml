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

open Format
open Options

let parse_file bin problem p =
  let configs = Queue.create () in
  let ch = open_in p in
  try
    while true do
      let line = input_line ch in
      let options =
        bin :: "-timelimit" :: (String.split_on_char ' ' line) @ [problem] in
      Queue.push (Array.of_list options) configs
    done;
    assert false
  with End_of_file ->
    close_in ch;
    configs

let () =
  let binary =
    try Sys.argv.(0)
    with _ -> assert false
  in
  (* fprintf fmt "binary is %s@." binary; *)
  let problem = Sys.argv.(Array.length Sys.argv -1) in

  let distribute =
    try String.equal Sys.argv.(1) "distribute"
    with _ -> false in
  if not distribute then Main_text.main ()
  else
    let procs = int_of_string Sys.argv.(2) in
    let runs = Hashtbl.create 17 in
    let configs = parse_file binary problem Sys.argv.(3) in
    let err = Unix.openfile "err" [Unix.O_RDWR;Unix.O_CREAT] 0o660 in

    let cpt = ref 0 in
    let running = ref 0 in
    try
      while true do
        if !running < procs && not (Queue.is_empty configs) then begin
          let conf = Queue.pop configs in
          let out = Unix.openfile (sprintf "%s_%d" "out" !cpt)
              [Unix.O_RDWR;Unix.O_CREAT;Unix.O_TRUNC] 0o660 in
          let pid = Unix.create_process binary conf Unix.stdin out err in

          (* printf "Running : ";
           * Array.iter (fun a -> printf "%s " a) conf;
           * printf "@."; *)

          Hashtbl.add runs pid (!cpt,out);
          incr cpt;
          incr running
        end
        else
          let pid,_ = Unix.wait () in
          let i,out = Hashtbl.find runs pid in

          (* let ch = Unix.in_channel_of_descr out in *)
          let ch = open_in (sprintf "%s_%d" "out" i) in

          set_binary_mode_in ch false;
          let s = try input_line ch with End_of_file -> "" in
          if String.equal s "unsat" || String.equal s "sat" then begin
            printf "%s@." s;
            raise Exit
          end;

          decr running
      done;
      assert false
    with
    | Exit | Unix.Unix_error (Unix.ECHILD,_,_) ->
      Hashtbl.iter (fun pid (cpt,out) ->
          begin try Unix.close out with _ -> () end;
          begin try Unix.kill pid Sys.sigkill with _ -> () end;
          Sys.remove (sprintf "%s_%d" "out" cpt)
        ) runs;
      Sys.remove "err"
    | _ -> assert false
