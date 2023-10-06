(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type 'a printer = Format.formatter -> 'a -> unit

module File : sig
  val touch: string -> unit
  (** [create fl] create an empty file of name [fl]. *)

  val scan_folder: string -> (string list * string list)
  (** [scan_folder fd] scan recursively the folder [fd]. *)

  val has_extension_in : string -> string list -> bool
  (** [has_extension_in fl exts] check if the [fl] has an extension
      in the list [exts]. *)
end = struct
  let touch fl =
    let ch = open_out fl in
    close_out ch

  let scan_folder path =
    let handle = Unix.opendir path in
    let rec aux files folders h =
      match Unix.readdir h with
      | exception End_of_file ->
        Unix.closedir h;
        List.sort String.compare files,
        List.sort String.compare folders
      | "." | ".." | "slow" | "cram.t" ->
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

  let pp fmt cmd =
    let pp_sep fmt () = Format.fprintf fmt "@ " in
    let pp_arg fmt = Format.fprintf fmt "%s" in
    let pp_args fmt = Format.pp_print_list ~pp_sep pp_arg fmt in
    Format.fprintf fmt "%s@ %a@ %%{input}" cmd.bin pp_args cmd.args
end

module Test : sig

  type params = {
    exclude: string list;
    filters: string list option;
    compare_should_succeed: bool;
    ae_should_succeed: bool;
  }

  type t = private {
    cmd: Cmd.t;
    pb_file: string;
    params: params
  }
  (** Type of a test. *)

  val base_params : params

  val make: cmd: Cmd.t -> pb_file: string -> params:params -> t
  (** Set up the test. *)

  val pp_expected_output: t printer
  (** Print the expect filename of the test. *)

  val pp_stanza: t printer
  (** Pretty print the dune test. *)
end = struct

  type params = {
    exclude: string list;
    filters: string list option;
    compare_should_succeed: bool;
    ae_should_succeed: bool;
  }

  type t = {
    cmd: Cmd.t;
    pb_file: string;
    params: params;
  }

  let base_params = {
    exclude = [];
    filters = None;
    compare_should_succeed = true;
    ae_should_succeed = true;
  }

  let make ~cmd ~pb_file ~params = {cmd; pb_file; params}

  let pp_output fmt tst =
    let filename = Filename.chop_extension tst.pb_file in
    let name = Cmd.name tst.cmd in
    Format.fprintf fmt "%s_%s.output" filename name

  let pp_expected_output fmt tst =
    let filename = Filename.chop_extension tst.pb_file in
    Format.fprintf fmt "%s.expected" filename

  let pp_stanza fmt tst =
    let pp_diff_command fmt tst =
      if tst.params.compare_should_succeed then
        Format.fprintf fmt "@[(diff %a %a)@]"
          pp_expected_output tst
          pp_output tst
      else
        Format.fprintf fmt
          "@[(ignore-stdout (with-accepted-exit-codes (not 0) (run diff %a %a)))@]"
          pp_expected_output tst
          pp_output tst
    in
    let accepted_ae_exit_code =
      if tst.params.ae_should_succeed
      then "0"
      else "1"
    in
    Format.fprintf fmt "\
@[<v 1>\
(rule@,\
(target %a)@,\
(deps (:input %s))@,\
(package alt-ergo)@,\
@[<v 1>(action@,\
@[<v 1>(chdir %%{workspace_root}@,\
@[<v 1>(with-stdout-to %%{target}@,\
@[<v 1>(ignore-stderr@,\
@[<v 1>(with-accepted-exit-codes %s@,\
@[<v 1>(run @[<hv>%a@])))))))@]@]@]@]@]@]@]@ \
@[<v 1>(rule@,\
@[<v 1>(deps %a)@,\
@[<v 1>(alias %s)@,\
@[<v 1>(package alt-ergo)@,\
@[<v 1>(action@ %a))@]@]@]@]@]"
      pp_output tst
      tst.pb_file
      accepted_ae_exit_code
      Cmd.pp tst.cmd
      pp_output tst
      (Cmd.group tst.cmd)
      pp_diff_command tst
end

module Batch : sig
  type t
  (** Type of a batch. *)

  val make:
    root:string -> path:string -> cmds:Cmd.t list
    -> pb_files: string list -> t
  (** Set up a batch of tests. *)

  val generate_expected_file : t -> unit
  (** Generate empty expected files for new tests. *)

  val pp_stanza : Format.formatter -> t -> unit
  (** Produce a dune file containing tests of the batch. *)
end = struct
  type t = {
    root: string;
    path: string;
    tests: Test.t list;
  }

  let filter (params : Test.params) cmd =
    not (List.exists (String.equal (Cmd.name cmd)) params.exclude) &&
    match params.filters with
    | Some filters -> List.exists (String.equal (Cmd.name cmd)) filters
    | None -> true

  let make ~root ~path ~cmds ~pb_files =
    let tests = List.fold_left (fun acc1 pb_file ->
        let params =
          List.fold_left (
            fun (acc : Test.params) ->
              function
              | "fail" ->
                {acc with compare_should_succeed = false}
              | "err" ->
                {acc with ae_should_succeed = false}
              | "dolmen" -> {
                  acc with
                  exclude = "legacy" :: acc.exclude;
                  filters = Some ["dolmen"]
                }
              | "models" -> {
                  acc with
                  exclude =
                    "legacy" :: "fpa" :: acc.exclude;
                  filters = Some ["tableaux"]
                }
              | "fpa" ->
                {acc with filters = Some ["fpa"]}
              | "optimize" ->
                {acc with
                 exclude = [];
                 filters = Some ["optimize"]}
              | _ ->
                (* TODO: This ugly trick prevent running AE on
                   tests with suffix `optimize` with inappropriate options.
                   We can run these tests only with the legacy frontend as
                   the maximize/minimize syntax isn't supported yet by the
                   frontend dolmen and we cannot use the (get-model)
                   statement with the legacy model. We have to remove this
                   trick as soon as dolmen can parse properly our syntax
                   of optimization constraints. *)
                match acc.filters with
                | Some ["optimize"] -> acc
                | _ ->
                  {acc with
                   exclude = "optimize" :: acc.exclude}
          )
            Test.base_params
            (String.split_on_char '.' pb_file)
        in
        List.fold_left (fun acc2 cmd ->
            if filter params cmd then
              Test.make ~cmd ~pb_file ~params :: acc2
            else
              acc2
          ) acc1 cmds) [] pb_files
    in
    {root; path; tests}

  (* Pretty print a dune file containing all the test of the batch. *)
  let pp_stanza : t printer =
    fun fmt batch ->
    let open Format in
    fprintf fmt "@ ";
    fprintf fmt "; File auto-generated by gentests@ @ ";
    fprintf fmt "; Auto-generated part begin@ ";
    let pp_sep fmt () = fprintf fmt "@ " in
    fprintf fmt "@[<v 2>(subdir %s@ %a)@]@ "
      batch.path
      (pp_print_list ~pp_sep Test.pp_stanza)  batch.tests;
    fprintf fmt "; Auto-generated part end"

  let generate_expected_file batch =
    List.iter (fun (test : Test.t) ->
        let pb_file =
          Format.asprintf "%a" Test.pp_expected_output test
          |> Filename.(concat (concat batch.root batch.path))
        in
        if not @@ Sys.file_exists pb_file then File.touch pb_file
      ) batch.tests
end

(* Test if a file is actually a problem for Alt-Ergo. *)
let is_a_problem file =
  File.has_extension_in file [".ae"; ".smt2"; ".pstm2"; ".zip"]

(* Generate a dune file for each subfolder of the path given as argument. *)
let rec generate root path cmds =
  let files, folders =
    File.scan_folder (Filename.concat root path)
  in
  let () = match List.filter is_a_problem files with
    | [] -> ()
    | pb_files -> (
        let batch = Batch.make ~root ~path ~cmds ~pb_files in
        Batch.generate_expected_file batch;
        Batch.pp_stanza Format.std_formatter batch
      ) in
  List.iter (fun folder ->
      let path = Filename.concat path folder in
      generate root path cmds
    ) folders

let () =
  let path =
    if Array.length Sys.argv >= 2 then
      Sys.argv.(1)
    else "."
  in
  let bin = "%{bin:alt-ergo}" in
  let timelimit = "--timelimit=2" in
  let shared =
    [ timelimit
    ; "--enable-assertions"
    ]
  in
  let solvers = [
    ("runtest-quick", "fpa",
     [ "--output=smtlib2"
     ; "--enable-theories fpa"
     ])
  ; ("runtest-quick", "dolmen",
     [ "--output=smtlib2"
     ; "--frontend dolmen" ])
  ; ("runtest-quick", "legacy",
     [ "--output=smtlib2"
     ; "--frontend legacy"
     ])
  ; ("runtest-quick", "tableaux",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver Tableaux" ])
  ; ("runtest-quick", "tableaux_cdcl",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver Tableaux-CDCL" ])
  ; ("runtest-quick", "cdcl",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver CDCL" ])
  ; ("runtest-ci", "ci_tableaux_cdcl_no_minimal_bj",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver CDCL-Tableaux"
     ; "--no-minimal-bj" ])
  ; ("runtest-ci", "ci_cdcl_tableaux_no_tableaux_cdcl_in_theories",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver CDCL-Tableaux"
     ; "--no-tableaux-cdcl-in-theories" ])
  ; ("runtest-ci", "ci_no_tableaux_cdcl_in_instantiation",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver CDCL-Tableaux"
     ; "--no-tableaux-cdcl-in-instantiation" ])
  ; ("runtest-ci", "ci_cdcl_tableaux_no_tableaux_cdcl_in_theories_and_instantiation",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver CDCL-Tableaux"
     ; "--no-tableaux-cdcl-in-theories"
     ; "--no-tableaux-cdcl-in-instantiation" ])
  ; ("runtest-ci", "ci_cdcl_tableaux_no_minimal_bj_no_tableaux_cdcl_in_theories\
                    _and_instantiation",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver CDCL-Tableaux"
     ; "--no-minimal-bj"
     ; "--no-tableaux-cdcl-in-theories"
     ; "--no-tableaux-cdcl-in-instantiation" ])
  ; ("runtest-ci", "ci_cdcl_no_minimal_bj",
     [ "--output=smtlib2"
     ; "--frontend dolmen"
     ; "--sat-solver CDCL"
     ; "--no-minimal-bj" ])
  ; ("runtest", "optimize",
     [ "--output=smtlib2"
     ; "--frontend legacy"
     ; "--dump-models"
     ; "--dump-models-on stdout"])]
  in
  let cmds = List.map (fun (group, name, args) ->
      let args = shared @ args in
      Cmd.make ~name ~group ~bin ~args) solvers
  in
  Format.fprintf Format.std_formatter "@[<v 0>";
  generate path "" cmds;
  Format.fprintf Format.std_formatter "@]@."
