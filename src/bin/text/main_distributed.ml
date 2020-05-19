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

open Format
open AltErgoLib.Options
open Alt_ergo_common

let parse_file bin problem p t =
  let total_time = float_of_int t in
  let configs = Queue.create () in
  try
    let nb_configs = ref 0 in
    let ch = open_in p in
    begin try
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
            bin :: "--timelimit" :: relative_tlimit :: options @ [problem] in
          incr nb_configs;
          Queue.push (Array.of_list config) configs
        done;
        assert false
      with End_of_file ->
        close_in ch;
        configs, !nb_configs
    end
  with Sys_error _ ->
    if get_debug_distrib () then
      fprintf fmt "[Warning] Options file %s not found,\
                   will continue with one \
                   thread and default configuration@." p;
    configs, 0

let parse_command () =
  try Parse_command.parse_cmdline_arguments ()
  with Parse_command.Exit_parse_command i -> exit i

let  () =
  parse_command ();
  let binary =
    try Sys.argv.(0)
    with _ -> assert false
  in
  let nb_procs = get_distributed_threads_number () in
  let problem = get_file () in

  if nb_procs = 0 then
    Main_text.main ()
  else
    let configs,nb_configs = parse_file binary problem (get_distributed_options_file ())
        (get_distributed_time_limit ()) in
    if nb_configs = 0 then
      Main_text.main ()
    else
      begin
        assert (nb_procs > 1);
        let runs = Hashtbl.create 17 in
        let err = Unix.openfile "err" [Unix.O_RDWR;Unix.O_CREAT] 0o660 in
        let cpt = ref 0 in
        let running = ref 0 in
        try
          while true do
            if !running < nb_procs && not (Queue.is_empty configs) then begin
              let conf = Queue.pop configs in
              let out = Unix.openfile (sprintf "%s_%d" "out" !cpt)
                  [Unix.O_RDWR;Unix.O_CREAT;Unix.O_TRUNC] 0o660 in
              let pid = Unix.create_process binary conf Unix.stdin out err in

              if get_debug_distrib () then begin
                fprintf fmt "Running configuration %d : " !cpt;
                Array.iter (fun a -> fprintf fmt "%s " a) conf;
                fprintf fmt "@.";
              end;

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
              end
              else if get_debug_distrib () then
                fprintf fmt "; result for run %d : %s@." i s;

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
          if get_debug_distrib () then begin
            fprintf fmt "@[<v 2>Read err :@,";
            let ch = open_in "err" in
            try while true do
                let s = input_line ch in
                fprintf fmt "%s@," s
              done;
            with End_of_file ->
              fprintf fmt "@.";
              close_in ch
          end;
          Sys.remove "err"
        | _ -> assert false
      end