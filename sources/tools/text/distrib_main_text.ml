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
open AltErgoLib.Options

let parse_file bin problem p t =
  let total_time = float_of_int t in
  let configs = Queue.create () in
  let ch = open_in p in
  try
    while true do
      let line = input_line ch in
      let time_limit, options =
        match (String.split_on_char ' ' line) with
        | []  -> assert false
        | [l] -> l, []
        | l :: opt -> l, opt
      in
      let relative_tlimit =
        string_of_float ((float_of_string time_limit) *. total_time) in
      let config =
        bin :: "-timelimit" :: relative_tlimit :: options @ [problem] in
      Queue.push (Array.of_list config) configs
    done;
    assert false
  with End_of_file ->
    close_in ch;
    configs


let  () =
  let binary =
    try Sys.argv.(0)
    with _ -> assert false
  in
  (* fprintf fmt "binary is %s@." binary; *)
  let procs = distrib_threads () in
  let problem = get_file () in

  if procs = 0 then
    Main_text.main ()
  else begin
    assert (procs > 0);
    let runs = Hashtbl.create 17 in
    let configs = parse_file binary problem (distrib_options_file ())
        (distrib_time_limit ()) in
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
          let i,_out = Hashtbl.find runs pid in

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
  end
