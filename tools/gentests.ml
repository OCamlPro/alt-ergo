(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2022 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

type 'a printer = Format.formatter -> 'a -> unit

module File : sig 
  val exists: string -> bool
  (** [exists fl] is true if and only if the file [fl] exists. *)

  val scan_folder: string -> (string list * string list)
  (** [scan_folder fd] scans recursively the folder [fd]. *)

  val read_all: in_channel -> string
  (** [read_all ch] reads completely the channel [ch] and 
      returns its content. *)

  val diff: string -> string -> string
  (** [diff file1 file2] performs a diff between [fl1] and [fl2]. *)

  val contains: string -> string -> bool
  (** [contains pattern fl] checks if the [fl] contains the pattern
      [pat]. *)

  val touch: string -> string -> bool
  (** [touch fl] creates the file [fl] if it doesn't exist yet. *)
  
  val cat: string printer 
  (** [cat fl] pretty prints the content of the file [fl]. *)
  
  val is_empty: string -> bool
  (** [is_empty file] check if the file [fl] is empty. *)
  
  val has_extension_in : string -> string list -> bool
  (** [has_extension_in fl exts] checks if the [fl] has an extension 
      in the list [exts]. *)
end = struct
  let exists fl =
    match open_in fl with
    | _ -> true
    | exception Sys_error _ -> false

  let scan_folder path =
    let handle = Unix.opendir path in
    let rec aux files folders h =
      match Unix.readdir h with
      | exception End_of_file ->
        Unix.closedir h;
        List.sort String.compare files,
        List.sort String.compare folders
      | "." | ".." ->
        aux files folders h
      | s ->
        let f = Filename.concat path s in
        let stat = Unix.stat f in
        begin match stat.st_kind with
          | Unix.S_REG -> aux (s :: files) folders h
          | Unix.S_DIR -> aux files (s :: folders) h
          | _ -> aux files folders h
        end
    in
    aux [] [] handle

  let read_all ch =
    let buf = Buffer.create 113 in
    try
      while true do
        Buffer.add_channel buf ch 30
      done;
      assert false
    with End_of_file ->
      Buffer.contents buf

  let diff fl1 fl2 =
    let cmd = Format.asprintf "diff %s %s" fl1 fl2 in
    let ch = Unix.open_process_in cmd in
    let res = read_all ch in
    ignore (Unix.close_process_in ch);
    res

  let contains pat fl =
    let cmd = Format.asprintf {|grep -q "%s" %s|} pat fl 
    in
    let ch = Unix.open_process_in cmd in
    let _ = read_all ch in
    let res = Unix.close_process_in ch in
    match res with
    | Unix.WEXITED 0 -> true
    | _ -> false
 
  let touch fl contents =
    if Sys.file_exists fl then
      true
    else
      let ch = open_out fl in
      output_string ch contents;
      close_out ch;
      false

  let cat fmt fl =
    let ch = open_in fl in
    try while true do
      let s = input_line ch in
      Format.fprintf fmt "%s@\n" s
    done
    with End_of_file ->
    Format.fprintf fmt "@."

  let is_empty fl =
    let ch = open_in fl in
    let res = 
      try
        let _ = input_char ch in
      false
    with End_of_file -> true in
    close_in ch;
    res

  let has_extension_in file =
    List.mem (Filename.extension file)
end

module Cmd : sig
  type t 
  (** Type of a command. *)

  val make : name: string -> group: string -> 
    bin: string -> args: string list -> t
  (** Create a new command. *)

  val name : t -> string
  (** Return the name of the command. *)

  val group : t -> string
  (** Return the group of the command. *)

  val digest: t -> string
  (** Produce a digest of the arguments of the command. *)

  val pp: t printer 
  (** Pretty print a command. *)
end = struct
  type t = {
    name: string;     (* Name of the command. *)
    group: string;
    bin: string;      (* Name of the binary. *)
    args: string list (* Argurments of the command. *)
  }

  let make ~name ~group ~bin ~args = {name; group; bin; args}

  let name cmd = cmd.name
  let group cmd = cmd.group

  let digest cmd = 
    List.fold_left (fun acc arg -> arg ^ acc) "" cmd.args
    |> Digest.string
    |> Digest.to_hex 

  let pp fmt cmd =
    let pp_sep fmt () = Format.fprintf fmt " @," in
    let pp_arg fmt = Format.fprintf fmt "%s" in
    let pp_args fmt = Format.pp_print_list ~pp_sep pp_arg fmt in
    Format.fprintf fmt "%s %a %%{input}" cmd.bin pp_args cmd.args
end

module Test : sig
  type t
  (** Type of a test. *)

  val make: cmd: Cmd.t -> pb_file: string -> t 
  (** Set up the test. *)

  val pp_output: t printer
  (** Pretty print the filename of the output of the test. *)
  
  val pp_expected_output: t printer
  (** Pretty print the filename of the expected output of the test. *)
  
  val pp_stanza: t printer
  (** Pretty print the dune test. *)
end = struct
  type t = {
    cmd: Cmd.t;
    pb_file: string
  }

  let make ~cmd ~pb_file = {cmd; pb_file}

  let pp_output fmt tst =
    let filename = Filename.chop_extension tst.pb_file in
    let name = Cmd.name tst.cmd in
    Format.fprintf fmt "%s_%s.output" filename name

  let pp_expected_output fmt tst =
    let filename = Filename.chop_extension tst.pb_file in
    Format.fprintf fmt "%s.expected" filename

  let pp_stanza fmt tst =
    Format.fprintf fmt 
    "@[<v 1>\
    (rule@ \
      (target %a)@ \
      (deps (:input %s))@ \
      (package alt-ergo-lib)@ \
      @[<v 1>(action@ \
        @[<v 1>(chdir %%{workspace_root}@ \
          @[<v 1>(with-stdout-to %%{target}@ \
            @[<v 1>(ignore-stderr@ \
              @[<v 1>(with-accepted-exit-codes 0@ \
                @[<v 1>(run %a)))))))@]@]@]@]@]@]@\n\
    @[<v 1>(rule@ \
      @[<v 1>(alias %s)@ \
      @[<v 1>(package alt-ergo-lib)@ \
      @[<v 1>(action (diff %a @, %a)))@]@]@]@]@."
    pp_output tst
    tst.pb_file
    Cmd.pp tst.cmd
    (Cmd.group tst.cmd)
    pp_expected_output tst 
    pp_output tst 
end

module Batch : sig
  type t
  (** Type of a batch. *)

  val make: path: string -> cmds: Cmd.t list 
    -> pb_files: string list -> t
  (** Set up a batch of tests. *)

  val generate_dune_file : t -> unit 
  (** Produce a dune file containing tests of the batch. *)
end = struct 
  type t = {
    path: string;
    cmds: Cmd.t list;
    tests: Test.t list;
  }
  
  let make ~path ~cmds ~pb_files =
    let tests = List.fold_left (fun acc1 pb_file -> 
      List.fold_left (fun acc2 cmd -> 
        (Test.make ~cmd ~pb_file) :: acc2
    ) acc1 cmds) [] pb_files
    in
    {path; cmds; tests}

  (* Pretty print a dune file containing all the test of the batch. *)
  let pp_stanza : t printer = 
    fun fmt batch ->
      let open Format in
      fprintf fmt "; File auto-generated by gentests@\n@\n";
      fprintf fmt "; Auto-generated part begin@\n";
      let pp_sep fmt () = fprintf fmt "@\n" in
      pp_print_list ~pp_sep Test.pp_stanza fmt batch.tests; 
      fprintf fmt "; Auto-generated part end@."

  let generate_dune_file batch =
    let dune_filename = Filename.concat batch.path "dune" in
    let digest =
      if File.exists dune_filename then
        Some (Digest.file dune_filename) 
      else None
    in
    let ch = open_out dune_filename in
    let fmt = Format.formatter_of_out_channel ch in
    pp_stanza fmt batch;
    let () = match digest with
    | Some d -> 
        if not @@ Digest.equal d (Digest.file dune_filename) then (
          Format.printf "Updating %s\n" dune_filename
        )
    | None -> 
        Format.printf "Creating %s\n" dune_filename 
    in
    close_out ch
end

(* Test if a file is actually a problem for Alt-Ergo. *)
let is_a_problem file = 
  File.has_extension_in file [".ae"; ".smt2"; ".pstm2"]

(* Generate a dune file for each subfolder of the path given as argument. *)
let rec generate path cmds =
  let files, folders = File.scan_folder path in
  let () = match List.filter is_a_problem files with
  | [] -> ()
  | pb_files -> (
    let batch = Batch.make ~path ~cmds ~pb_files in
    Batch.generate_dune_file batch 
  ) in
  List.iter (fun path ->
    generate path cmds 
  ) (List.map (Filename.concat path) folders)

let () =
  let path = 
    if Array.length Sys.argv >= 2 then
      Sys.argv.(1)
    else "."
  in
  let bin = "alt-ergo" in
  let solvers = [
    ("runtest", "tableaux", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver Tableaux" ])
  ; ("runtest", "tableaux_cdcl", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver Tableaux-CDCL" ])
  ; ("runtest", "cdcl", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL" ])
  ; ("runtest", "cdcl_tableaux", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL-Tableaux" ])
  ; ("runtest-ci", "ci_tableaux_cdcl_no_minimal_bj", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL-Tableaux"
    ; "--no-minimal-bj" ])
  ; ("runtest-ci", "ci_cdcl_tableaux_no_tableaux_cdcl_in_theories", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL-Tableaux"
    ; "--no-tableaux-cdcl-in-theories" ])
  ; ("runtest-ci", "ci_no_tableaux_cdcl_in_instantiation", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL-Tableaux"
    ; "--no-tableaux-cdcl-in-instantiation" ])
  ; ("runtest-ci", "ci_cdcl_tableaux_no_tableaux_cdcl_in_theories_and_instantiation", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL-Tableaux"
    ; "--no-tableaux-cdcl-in-theories"
    ; "--no-tableaux-cdcl-in-instantiation" ])
  ; ("runtest-ci", "ci_cdcl_tableaux_no_minimal_bj_no_tableaux_cdcl_in_theories\
    _and_instantiation", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL-Tableaux"
    ; "--no-minimal-bj"
    ; "--no-tableaux-cdcl-in-theories"
    ; "--no-tableaux-cdcl-in-instantiation" ])
  ; ("runtest-ci", "ci_tableaux", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver Tableaux" ])
  ; ("runtest-ci", "ci_tableaux_cdcl", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver Tableaux-CDCL" ])
  ; ("runtest-ci", "ci_cdcl", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver CDCL" ])
  ; ("runtest-ci", "ci_cdcl_no_minimal_bj", [
      "--output=smtlib2"
    ; "--timelimit=1"
    ; "--sat-solver Tableaux-CDCL"
    ; "--no-minimal-bj" ])] 
  in
  let cmds = List.map (fun (group, name, args) -> 
    Cmd.make ~name ~group ~bin ~args) solvers 
  in
  generate path cmds


