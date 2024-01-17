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

open AltErgoLib
open Options
open Cmdliner

exception Error of bool * string

(* Exception used to exit with corresponding retcode *)
exception Exit_parse_command of int

let instantiation_heuristic_parser = function
  | "normal" -> Ok INormal
  | "auto" -> Ok IAuto
  | "greedy" -> Ok IGreedy
  | s ->
    Error (`Msg ("Option --instantiation-heuristic does not accept\
                  the argument \"" ^ s))

let instantiation_heuristic_to_string = function
  | INormal -> "normal"
  | IAuto -> "auto"
  | IGreedy -> "greedy"

let instantiation_heuristic_printer fmt instantiation_heuristic =
  Format.fprintf fmt "%s"
    (instantiation_heuristic_to_string instantiation_heuristic)

let instantiation_heuristic_conv =
  Arg.conv ~docv:"VAL"
    (instantiation_heuristic_parser, instantiation_heuristic_printer)

(* When adding another parser, remember to change this list too as it
   is used in the documentation *)
let formats_list =
  ["native", Native;
   "altergo", Native;
   "alt-ergo", Native;
   "smtlib2", Smtlib2 `Latest;
   "smt-lib2", Smtlib2 `Latest;
   "psmt2", Smtlib2 `Poly;
   "smtlib2-v2.6", Smtlib2 `V2_6;
   "why3", Why3]

let format_parser s =
  try
    Ok (My_list.assoc String.equal s formats_list)
  with
    Not_found ->
    Error (`Msg (Format.sprintf
                   "The format %s is not accepted as input/output" s))

let format_to_string = function
  | Native -> "native"
  | Smtlib2 `V2_6 -> "smtlib2-v2.6"
  | Smtlib2 `Poly -> "psmt2"
  | Smtlib2 `Latest -> "smtlib2"
  | Why3 -> "why3"
  | Unknown s -> Format.sprintf "Unknown %s" s

let format_printer fmt format =
  Format.fprintf fmt "%s" (format_to_string format)

let format_conv = Arg.conv ~docv:"FMT" (format_parser, format_printer)

let model_type_parser = function
  | "value" -> Ok Value
  | "constraints" -> Ok Constraints
  | s ->
    Error (`Msg (Format.sprintf
                   "The model kind %s is invalid. Only \"value\" and \
                    \"constraints\" are allowed" s))

let model_type_printer fmt format =
  Format.fprintf fmt "%s"
    (match format with
     | Value -> "value"
     | Constraints -> "constaints")

let model_type_conv =
  Arg.conv ~docv:"MTYP" (model_type_parser, model_type_printer)

module Rule = struct
  type t = RParsing | RTyping | RSat | RCC | RArith | RNone

  let all = [RParsing; RTyping; RSat; RCC; RArith; RNone]

  let value_of_rule = function
    | RParsing -> 0
    | RTyping -> 1
    | RSat -> 2
    | RCC -> 3
    | RArith -> 4
    | RNone -> -1

  let show = function
    | RParsing -> "parsing"
    | RTyping -> "typing"
    | RSat -> "sat"
    | RCC -> "cc"
    | RArith -> "arith"
    | RNone -> "none"

  let mk flag = Options.set_rule (value_of_rule flag)

  let flag_term =
    let enum_conv =
      List.map (fun v -> (show v, v)) all
      |> Arg.enum
    in
    let doc =
      Format.sprintf "Output rule used on stderr, $(docv) must be %s."
        (Arg.doc_alts (List.map show all))
    in
    let docv = "TR" in
    Arg.(value & opt enum_conv RNone & info ["rule"] ~docv ~doc)
end

module Debug = struct
  type t =
    | Debug
    | Ac
    | Adt
    | Arith
    | Arrays
    | Bitv
    | Sum
    | Ite
    | Cc
    | Combine
    | Constr
    | Explanation
    | Fm
    | Fpa
    | Gc
    | Interpretation
    | Intervals
    | Matching
    | Sat
    | Split
    | Triggers
    | Types
    | Typing
    | Uf
    | Unsat_core
    | Use
    | Warnings
    | Commands
    | Optimize
  [@@deriving eq]

  let all = [
    Debug; Ac; Adt; Arith; Arrays; Bitv; Sum; Ite;
    Cc; Combine; Constr; Explanation; Fm; Fpa; Gc;
    Interpretation; Intervals; Matching; Sat; Split; Triggers;
    Types; Typing; Uf; Unsat_core; Use; Warnings;
    Commands; Optimize
  ]

  let show = function
    | Debug -> "debug"
    | Ac -> "ac"
    | Adt -> "adt"
    | Arith -> "arith"
    | Arrays -> "arrays"
    | Bitv -> "bitv"
    | Sum -> "sum"
    | Ite -> "ite"
    | Cc -> "cc"
    | Combine -> "combine"
    | Constr -> "constr"
    | Explanation -> "explanation"
    | Fm -> "fm"
    | Fpa -> "fpa"
    | Gc -> "gc"
    | Interpretation -> "interpretation"
    | Intervals -> "intervals"
    | Matching -> "matching"
    | Sat -> "sat"
    | Split -> "split"
    | Triggers -> "triggers"
    | Types -> "types"
    | Typing -> "typing"
    | Uf -> "uf"
    | Unsat_core -> "unsat-core"
    | Use -> "use"
    | Warnings -> "warnings"
    | Commands -> "commands"
    | Optimize -> "optimize"

  let mk ~verbosity flags =
    List.concat flags
    |> List.iter (function
        | Debug -> Options.set_debug true
        | Ac -> Options.set_debug_ac true
        | Adt -> Options.set_debug_adt true
        | Arith -> Options.set_debug_arith true
        | Arrays -> Options.set_debug_arrays true
        | Bitv -> Options.set_debug_bitv true
        | Sum -> Options.set_debug_sum true
        | Ite -> Options.set_debug_ite true
        | Cc -> Options.set_debug_cc true
        | Combine -> Options.set_debug_combine true
        | Constr -> Options.set_debug_constr true
        | Explanation -> Options.set_debug_explanations true
        | Fm -> Options.set_debug_fm true
        | Fpa -> Options.set_debug_fpa verbosity
        | Gc -> Options.set_debug_gc true
        | Interpretation -> Options.set_debug_interpretation true
        | Intervals -> Options.set_debug_intervals true
        | Matching -> Options.set_debug_matching verbosity
        | Sat -> Options.set_debug_sat true
        | Split -> Options.set_debug_split true
        | Triggers -> Options.set_debug_triggers true
        | Types -> Options.set_debug_types true
        | Typing -> Options.set_debug_typing true
        | Uf -> Options.set_debug_uf true
        | Unsat_core -> Options.set_debug_unsat_core true
        | Use -> Options.set_debug_use true
        | Warnings -> Options.set_debug_warnings true
        | Commands -> Options.set_debug_commands true
        | Optimize -> Options.set_debug_optimize true
      )

  let light_flag_term, medium_flag_term, full_flag_term =
    let enum_conv =
      List.map (fun v -> (show v, v)) all
      |> Arg.enum
      |> Arg.list
    in
    let light_doc =
      Format.sprintf
        "Set the debugging flags with light verbosity, $(docv) must be %s."
        (Arg.doc_alts (List.map show all))
    in
    let medium_doc =
      Format.sprintf
        "Set the debugging flags with medium verbosity, $(docv) must be %s."
        (Arg.doc_alts (List.map show all))
    in
    let full_doc =
      Format.sprintf
        "Set the debugging flags with full verbosity, $(docv) must be %s."
        (Arg.doc_alts (List.map show all))
    in
    let docv = "DEBUG" in
    Arg.(value & opt_all enum_conv [] & info ["d"; "debug"] ~docv
           ~doc:light_doc),
    Arg.(value & opt_all enum_conv [] & info ["dd"; "ddebug"] ~docv
           ~doc:medium_doc),
    Arg.(value & opt_all enum_conv [] & info ["ddd"; "dddebug"] ~docv
           ~doc:full_doc)
end

let mk_case_split_opt case_split_policy enable_adts_cs max_split ()
  =
  let res =
    match case_split_policy with
    | "after-theory-assume" -> Ok(Util.AfterTheoryAssume)
    | "before-matching" -> Ok(Util.BeforeMatching)
    | "after-matching" -> Ok(Util.AfterMatching)
    | _ -> Error ("Bad value '" ^ case_split_policy ^
                  "' for option --case-split-policy")
  in
  let max_split = Numbers.Q.from_string max_split in
  match res with
  | Ok(case_split_policy) ->
    set_max_split max_split;
    set_case_split_policy case_split_policy;
    set_enable_adts_cs enable_adts_cs;
    `Ok()
  | Error m -> `Error(false, m)

let mk_context_opt replay replay_all_used_context replay_used_context
    save_used_context
  =
  set_save_used_context save_used_context;
  set_replay replay;
  set_replay_all_used_context replay_all_used_context;
  set_replay_used_context replay_used_context;
  `Ok()

let mk_execution_opt input_format parse_only ()
    preludes no_locs_in_answers colors_in_output no_headers_in_output
    no_formatting_in_output no_forced_flush_in_output pretty_output
    type_only type_smt2
  =
  let answers_with_loc = not no_locs_in_answers in
  let output_with_colors = colors_in_output || pretty_output in
  let output_with_headers = (not no_headers_in_output) || pretty_output in
  let output_with_formatting = (not no_formatting_in_output) || pretty_output in
  let output_with_forced_flush =
    (not no_forced_flush_in_output) && (not pretty_output) in
  set_answers_with_loc answers_with_loc;
  set_output_with_colors output_with_colors;
  set_output_with_headers output_with_headers;
  set_output_with_formatting output_with_formatting;
  set_output_with_forced_flush output_with_forced_flush;
  set_input_format input_format;
  set_parse_only parse_only;
  set_type_only type_only;
  set_type_smt2 type_smt2;
  set_preludes preludes;
  `Ok()

let mk_internal_opt
    disable_weaks enable_assertions warning_as_error continue_on_error gc_policy
  =
  let gc_policy = match gc_policy with
    | 0 | 1 | 2 -> gc_policy
    | _ ->
      Printer.print_wrn "Gc_policy value must be 0[default], 1 or 2";
      0
  in
  set_disable_weaks disable_weaks;
  set_enable_assertions enable_assertions;
  set_warning_as_error warning_as_error;
  set_exit_on_error (not continue_on_error);
  `Ok(gc_policy)

let mk_limit_opt age_bound fm_cross_limit timelimit_interpretation
    steps_bound timelimit timelimit_per_goal
  =
  let set_limit t d =
    match t with
    | Some t ->
      if Sys.win32 then (
        Printer.print_wrn
          "timelimit not supported on Win32 (ignored)";
        d
      )
      else t
    | None -> d
  in
  if steps_bound < -1 then
    `Error (false, "--steps-bound argument should be positive")
  else
    let fm_cross_limit = Numbers.Q.from_string fm_cross_limit in
    let timelimit = set_limit timelimit 0. in
    let timelimit_interpretation = set_limit timelimit_interpretation 0. in
    set_age_bound age_bound;
    set_fm_cross_limit fm_cross_limit;
    set_timelimit_interpretation timelimit_interpretation;
    set_steps_bound steps_bound;
    Steps.set_steps_bound steps_bound;
    set_timelimit timelimit;
    set_timelimit_per_goal timelimit_per_goal;
    `Ok()

let mk_output_opt
    interpretation use_underscore objectives_in_interpretation unsat_core
    output_format model_type () () () () ()
  =
  set_infer_output_format (Option.is_none output_format);
  let output_format = match output_format with
    | None -> Native
    | Some fmt -> fmt
  in
  let model_type = match model_type with
    | None -> Value
    | Some v -> v
  in
  set_interpretation interpretation;
  set_interpretation_use_underscore use_underscore;
  set_objectives_in_interpretation objectives_in_interpretation;
  set_unsat_core unsat_core;
  set_output_format output_format;
  set_model_type model_type;
  `Ok()

let mk_profiling_opt cumulative_time_profiling profiling
    profiling_plugin get_verbose
  =
  let profiling, profiling_period = match profiling with
    | Some f -> true, f
    | None -> false, 0.
  in
  set_profiling profiling profiling_period;
  set_profiling_plugin profiling_plugin;
  set_verbose get_verbose;
  set_cumulative_time_profiling cumulative_time_profiling;
  `Ok()

let mk_quantifiers_opt instantiation_heuristic instantiate_after_backjump
    max_multi_triggers_size nb_triggers
    no_ematching no_user_triggers normalize_instances triggers_var
  =
  set_no_user_triggers no_user_triggers;
  set_no_ematching no_ematching;
  set_nb_triggers nb_triggers;
  set_normalize_instances normalize_instances;
  set_instantiation_heuristic instantiation_heuristic;
  set_instantiate_after_backjump instantiate_after_backjump;
  set_max_multi_triggers_size max_multi_triggers_size;
  set_triggers_var triggers_var;
  `Ok()

let mk_sat_opt get_bottom_classes disable_flat_formulas_simplification
    enable_restarts no_arith_matching no_backjumping
    no_backward no_decisions no_decisions_on
    no_minimal_bj no_sat_learning
  =
  let arith_matching = not no_arith_matching in
  let mk_no_decisions_on ndo =
    List.fold_left
      (fun set s ->
         match s with
         | "" -> set
         | s -> Util.SS.add s set
      ) Util.SS.empty (Str.split (Str.regexp ",") ndo)
  in
  let no_decisions_on = mk_no_decisions_on no_decisions_on in
  let minimal_bj = not no_minimal_bj in

  set_arith_matching arith_matching;
  set_bottom_classes get_bottom_classes;
  set_disable_flat_formulas_simplification
    disable_flat_formulas_simplification;
  set_enable_restarts enable_restarts;
  set_minimal_bj minimal_bj;
  set_no_backjumping no_backjumping;
  set_no_backward no_backward;
  set_no_decisions no_decisions;
  set_no_decisions_on no_decisions_on;
  set_no_sat_learning no_sat_learning;
  ()

let mk_term_opt disable_ites inline_lets rewriting no_term_like_pp
  =
  set_rewriting rewriting;
  set_term_like_pp (not no_term_like_pp);
  set_disable_ites disable_ites;
  set_inline_lets inline_lets;
  `Ok()

let mk_theory_opt () no_contracongru
    no_fm no_nla no_tcp no_theory restricted tighten_vars
    _use_fpa (theories)
  =
  set_no_ac (not (List.exists (Theories.equal Theories.AC) theories));
  set_no_fm no_fm;
  set_no_nla no_nla;
  set_no_tcp no_tcp;
  set_no_theory no_theory;
  set_restricted restricted;
  set_disable_adts
    (not (List.exists (Theories.equal Theories.ADT) theories));
  set_tighten_vars tighten_vars;
  set_no_contracongru no_contracongru;
  set_theory_preludes (Theories.preludes theories);
  `Ok()

let halt_opt version_info where =
  let handle_where w =
    let res = match w with
      | "plugins" -> `Ok Config.plugins_locations
      | "preludes" -> `Ok Config.preludes_locations
      | _ -> `Error
               ("Option --where does not accept the argument \"" ^ w ^
                "\"\nAccepted options are plugins or preludes")
    in
    match res with
    | `Ok paths ->
      Printer.print_std "@[<v>%a@]@."
        Format.(pp_print_list ~pp_sep:pp_print_cut pp_print_string)
        paths
    | `Error m -> raise (Error (false, m))
  in
  let handle_version_info vi =
    if vi then (
      Printer.print_std
        "@[<v 0>Version          = %s@,\
         Release commit   = %s@]@."
        Version._version
        Version._release_commit;
    )
  in
  try
    match where with
    | Some w -> handle_where w; `Ok true
    | None -> if version_info then (handle_version_info version_info; `Ok true)
      else `Ok false
  with Failure f -> `Error (false, f) (* TODO(Steven): dead code? *)
     | Error (b, m) -> `Error (b, m)

let get_verbose_t =
  let doc = "Set the verbose mode." in
  Arg.(value & flag & info ["v"; "verbose"] ~doc)

let mk_opts file () () debug_flags ddebug_flags dddebug_flags rule () halt_opt
    (gc) () () () () () () () () =
  Debug.mk ~verbosity:1 debug_flags;
  Debug.mk ~verbosity:2 ddebug_flags;
  Debug.mk ~verbosity:3 dddebug_flags;
  Rule.mk rule;
  if halt_opt then `Ok false
  (* If save_used_context was invoked as an option it should
       automatically set unsat_core to true *)
  else begin
    if get_save_used_context () then set_unsat_core true;
    (match file with
     | Some f ->
       let base_file = try
           Filename.chop_extension f
         with Invalid_argument _ -> f
       in
       set_file f;
       set_session_file (base_file^".agr");
       set_used_context_file base_file;
     | _ -> ()
    );

    Gc.set { (Gc.get()) with Gc.allocation_policy = gc };
    `Ok true
  end

let mk_output_channel_opt regular_output diagnostic_output =
  Options.Output.(create_channel regular_output |> set_regular);
  Options.Output.(create_channel diagnostic_output |> set_diagnostic);
  `Ok()

(* Custom sections *)

let s_debug = "DEBUG OPTIONS"
let s_case_split = "CASE SPLIT OPTIONS"
let s_context = "CONTEXT OPTIONS"
let s_execution = "EXECUTION OPTIONS"
let s_internal = "INTERNAL OPTIONS"
let s_halt = "HALTING OPTIONS"
let s_limit = "LIMIT OPTIONS"
let s_output = "OUTPUT OPTIONS"
let s_profiling = "PROFILING OPTIONS"
let s_quantifiers = "QUANTIFIERS OPTIONS"
let s_sat = "SAT OPTIONS"
let s_term = "TERM OPTIONS"
let s_theory = "THEORY OPTIONS"
let s_fmt = "FORMATTER OPTIONS"
let s_models = "MODEL OPTIONS"


(* Parsers *)

let parse_case_split_opt =

  let docs = s_case_split in

  let case_split_policy =
    let doc = Format.sprintf
        "Case-split policy. Set the case-split policy to use. \
         Possible values are %s."
        (Arg.doc_alts
           ["after-theory-assume"; "before-matching"; "after-matching"]) in
    let docv = "PLCY" in
    Arg.(value & opt string "after-theory-assume" &
         info ["case-split-policy"] ~docv ~docs ~doc) in

  let enable_adts_cs =
    let doc = "Enable case-split for Algebraic Datatypes theory." in
    Arg.(value & flag & info ["enable-adts-cs"] ~docs ~doc) in

  let enable_sat_cs =
    let doc = "Enable case-split in the SAT solver (Experts only)" in
    Term.(
      const set_enable_sat_cs $
      Arg.(value & flag & info ["enable-sat-cs"] ~docs ~doc)
    )
  in

  let max_split =
    let dv = Numbers.Q.to_string (get_max_split ()) in
    let doc =
      Format.sprintf "Maximum size of case-split." in
    let docv = "VAL" in
    Arg.(value & opt string dv & info ["max-split"] ~docv ~docs ~doc) in

  Term.(ret (const mk_case_split_opt $
             case_split_policy $ enable_adts_cs $ max_split $ enable_sat_cs))

let parse_context_opt =

  let docs = s_context in

  let replay =
    let doc = "Replay session saved in $(i,file_name.agr)." in
    Arg.(value & flag & info ["replay"] ~docs ~doc) in

  let replay_all_used_context =
    let doc =
      "Replay with all axioms and predicates saved in $(i,.used) files \
       of the current directory." in
    Arg.(value & flag & info ["replay-all-used-context"] ~docs ~doc) in

  let replay_used_context =
    let doc = "Replay with axioms and predicates saved in $(i,.used) file." in
    Arg.(value & flag & info ["r"; "replay-used-context"] ~doc) in

  let save_used_context =
    let doc = "Save used axioms and predicates in a $(i,.used) file. \
               This option implies $(b,--unsat-core)." in
    Arg.(value & flag & info ["s"; "save-used-context"] ~doc) in

  Term.(ret (const mk_context_opt $
             replay $ replay_all_used_context $ replay_used_context $
             save_used_context
            ))

let parse_execution_opt =

  let docs = s_execution in

  let input_format =
    let doc = Format.sprintf
        "Set the default input format to $(docv) and must be %s. \
         Useful when the extension does not allow to automatically select \
         a parser (eg. JS mode, GUI mode, ...)."
        (Arg.doc_alts (fst @@ List.split formats_list)) in
    let docv = "FMT" in
    Arg.(value & opt (some format_conv) None & info ["i"; "input"] ~docv ~doc)
  in

  let parse_only =
    let doc = "Stop after parsing." in
    Arg.(value & flag & info ["parse-only"] ~docs ~doc) in

  let parsers =
    let load_parser verbose path =
      try
        MyDynlink.load verbose path "parser";
        Ok ()
      with
        Errors.Error e ->
        Error (Format.asprintf "%a" Errors.report e)
    in
    let load_parsers verbose paths =
      List.fold_left
        (fun res path ->
           Result.bind res (fun () -> load_parser verbose path))
        (Ok ()) paths
    in
    let doc = "Register a new parser for Alt-Ergo." in
    let arg =
      Arg.(value & opt_all string [] &
           info ["add-parser"] ~docs ~doc)
    in
    let term = Term.(const load_parsers $ get_verbose_t $ arg) in
    Term.term_result' term
  in

  let preludes =
    let parse_prelude p =
      if Sys.file_exists p then
        if Sys.is_directory p then
          Fmt.error "'%s' is a directory" p
        else
          Ok p
      else
        match Config.lookup_prelude p with
        | Some p' ->
          begin if Compat.String.starts_with ~prefix:"b-set-theory" p then
              Printer.print_wrn ~header:true
                "Support for the B set theory is deprecated since version \
                 2.5.0 and may be removed in a future version. If you are \
                 actively using it, please make yourself known to the Alt-Ergo \
                 developers by writing to <alt-ergo@ocamlpro.com>."
            else if Compat.String.starts_with ~prefix:"fpa-theory" p then
              Printer.print_wrn ~header:true
                "@[Support for the FPA theory has been integrated as a \
                 builtin theory prelude in version 2.5.0 and is enabled \
                 by default.\
                 This option and the '%s'@ prelude will \ be removed in a \
                 later version.@]" p
          end;

          Ok p'
        | None ->
          Error (
            Format.asprintf
              "cannot load prelude '%s': no such file"
              p)
    in
    let prelude =
      Arg.(conv' (parse_prelude, conv_printer string))
    in
    let doc =
      "Add a file that will be loaded as a prelude. The command is \
       cumulative, and the order of successive preludes is preserved." in
    Arg.(value & opt_all prelude (get_preludes ()) &
         info ["prelude"] ~docs ~doc) in

  let no_locs_in_answers =
    let doc =
      "Do not show the locations of goals when printing solver's answers." in
    Arg.(value & flag & info ["no-locs-in-answers"] ~docs ~doc) in

  let colors_in_output =
    let doc =
      "Print output with colors." in
    Arg.(value & flag & info ["colors-in-output"] ~docs ~doc) in

  let no_headers_in_output =
    let doc =
      "Print output without headers." in
    Arg.(value & flag & info ["no-headers-in-output"] ~docs ~doc) in

  let no_formatting_in_output =
    let doc =
      "Don not use formatting rule in output." in
    Arg.(value & flag & info ["no-formatting-in-output"] ~docs ~doc) in

  let no_forced_flush_in_output =
    let doc =
      "Print output without forced flush at the end of each print." in
    Arg.(value & flag & info ["no-forced-flush-in-output"] ~docs ~doc) in

  let pretty_output =
    let doc =
      "Print output with formatting rules, headers and colors" in
    Arg.(value & flag & info ["p"; "pretty-output"] ~doc) in

  let type_only =
    let doc = "Stop after typing." in
    Arg.(value & flag & info ["type-only"] ~docs ~doc) in

  let type_smt2 =
    let doc = "Stop after SMT2 typing." in
    Arg.(value & flag & info ["type-smt2"] ~docs ~doc) in


  Term.(ret (const mk_execution_opt $
             input_format $ parse_only $ parsers $ preludes $
             no_locs_in_answers $ colors_in_output $ no_headers_in_output $
             no_formatting_in_output $ no_forced_flush_in_output $
             pretty_output $ type_only $ type_smt2
            ))

let parse_halt_opt =

  let docs = s_halt in

  let version_info =
    let doc = "Print some info about this version \
               (version, date released, date commited) ." in
    Arg.(value & flag & info ["version-info"] ~docs ~doc) in

  let where =
    let doc = Format.sprintf
        "Print the directory of $(docv). Possible arguments are \
         %s." (Arg.doc_alts ["plugins"; "preludes"]) in
    let docv = "DIR" in
    Arg.(value & opt (some string) None & info ["where"] ~docv ~docs ~doc) in

  Term.(ret (const halt_opt $
             version_info $ where
            ))

let parse_internal_opt =

  let docs = s_internal in

  let disable_weaks =
    let doc =
      "Prevent the GC from collecting hashconsed data structrures that are \
       not reachable (useful for more determinism)." in
    Arg.(value & flag & info ["disable-weaks"] ~docs ~doc) in

  let enable_assertions =
    let doc = "Enable verification of some heavy invariants." in
    Arg.(value & flag & info ["enable-assertions"] ~docs ~doc) in

  let warning_as_error =
    let doc = "Enable warning as error" in
    Arg.(value & flag & info ["warning-as-error"] ~docs ~doc) in

  let continue_on_error =
    let doc = "Sets Alt-ergo's behavior to continue on errors" in
    Arg.(value & flag & info ["continue-on-error"] ~docs ~doc) in

  let gc_policy =
    let doc =
      "Set the gc policy allocation. 0 = next-fit policy, 1 = \
       first-fit policy, 2 = best-fit policy. See the Gc module \
       of the OCaml distribution for more informations." in
    let docv = "PLCY" in
    Arg.(value & opt int 0 & info ["gc-policy"] ~docv ~docs ~doc) in

  Term.(ret (const mk_internal_opt $
             disable_weaks $ enable_assertions $
             warning_as_error $ continue_on_error $ gc_policy
            ))

let parse_limit_opt =

  let docs = s_limit in

  let age_bound =
    let doc = "Set the age limit bound." in
    let docv = "AGE" in
    Arg.(value & opt int (get_age_bound ()) &
         info ["age-bound"] ~docv ~docs ~doc) in

  let fm_cross_limit =
    (* TODO : Link this to Alt-Ergo numbers *)
    let dv = Numbers.Q.to_string (get_fm_cross_limit ()) in
    let doc = Format.sprintf
        "Skip Fourier-Motzkin variables elimination steps that may produce \
         a number of inequalities that is greater than the given limit. \
         However, unit eliminations are always done." in
    let docv = "VAL" in
    Arg.(value & opt string dv & info ["fm-cross-limit"] ~docv ~docs ~doc) in

  let timelimit_interpretation =
    let doc = "Set the time limit to $(docv) seconds for model generation \
               (not supported on Windows)." in
    let docv = "SEC" in
    Arg.(value & opt (some float) None &
         info ["timelimit-interpretation"] ~docv ~docs ~doc) in

  let steps_bound =
    let doc = "Set the maximum number of steps." in
    let docv = "STEPS" in
    Arg.(value & opt int (get_steps_bound ()) &
         info ["S"; "steps-bound"] ~docv ~doc) in

  let timelimit =
    let doc =
      "Set the time limit to $(docv) seconds (not supported on Windows)." in
    let docv = "VAL" in
    Arg.(value & opt (some float) None & info ["t"; "timelimit"] ~docv ~doc) in

  let timelimit_per_goal =
    let doc =
      "Set the timelimit given by the $(i,--timelimit) option to apply \
       for each goal, in case of multiple goals per \
       file. In this case, time spent in preprocessing is separated from \
       resolution time. Not relevant for GUI-mode." in
    Arg.(value & flag & info ["timelimit-per-goal"] ~docs ~doc) in

  Term.(ret (const mk_limit_opt $
             age_bound $ fm_cross_limit $ timelimit_interpretation $
             steps_bound $ timelimit $ timelimit_per_goal
            ))

let parse_output_opt =

  let docs = s_output in

  (* Use the --interpretation and --produce-models (which is equivalent to
     --interpretation last) to determine the interpretation value. *)
  let interpretation, dump_models, dump_models_on, verify_models, frontend =
    let interpretation =
      let doc = Format.sprintf
          "Best effort support for counter-example generation. \
           $(docv) must be %s. %s shows the first computed interpretation. \
           %s compute an interpretation before every decision, \
           and %s only before returning unknown. \
           Note that $(b, --max-split) limitation will \
           be ignored in model generation phase."
          (Arg.doc_alts
             ["none"; "first"; "every"; "last"])
          (Arg.doc_quote "first") (Arg.doc_quote "every")
          (Arg.doc_quote "last") in
      let docv = "VAL" in
      let interpretation =
        Arg.enum
          [ "none", INone
          ; "first", IFirst
          ; "every", IEvery
          ; "last", ILast
          ]
      in
      Arg.(value & opt interpretation INone &
           info ["interpretation"] ~docv ~docs:s_models ~doc)
    in

    let produce_models =
      let doc =
        "Enable model generation (equivalent to --interpretation last)."
      in
      Arg.(value & flag & info ["produce-models"] ~doc ~docs:s_models)
    in

    let verify_models =
      let doc =
        "Verify generated models."
      in
      Arg.(value & flag & info ["verify-models"] ~doc ~docs:s_models)
    in


    let frontend =
      let doc =
        "Select the parsing and typing frontend. Support for non-default \
         frontends is deprecated and will be removed in the next release."
      in
      let docv = "FTD" in
      let deprecated =
        "this option is deprecated and will be ignored in the \
         next version"
      in
      Arg.(value & opt string "dolmen" &
           info ["frontend"] ~docv ~docs:s_execution ~doc ~deprecated)
    in

    let dump_models =
      let doc =
        "Display a model each time the result is unknown (implies \
         --interpretation last)"
      in
      Arg.(value & flag & info ["dump-models"] ~doc ~docs:s_models)
    in

    let dump_models_on =
      let doc =
        "Select a channel to output the models dumped by the option \
         --dump-model."
      in
      let docv = "VAL" in
      let chan =
        Arg.conv
          ~docv
          (
            (fun s -> Ok (Output.create_channel s)),
            (fun fmt f -> Format.pp_print_string fmt (Output.to_string f))
          )
      in
      Arg.(value & opt chan (Output.create_channel "stderr") &
           info ["dump-models-on"] ~docv ~docs:s_models ~doc)
    in

    let mk_interpretation interpretation produce_models dump_models =
      match interpretation with
      | INone when produce_models || dump_models -> ILast
      | interpretation -> interpretation
    in
    Term.(
      const mk_interpretation $ interpretation $
      produce_models $ dump_models
    ),
    dump_models,
    dump_models_on,
    verify_models,
    frontend
  in

  (* Use the --sat-solver to determine the sat solver. *)
  let sat_solver =
    let sat_solver : _ Arg.conv =
      let parse = function
        | "CDCL" | "satML" ->
          Ok Util.CDCL
        | "CDCL-Tableaux" | "satML-Tableaux"
        | "CDCL-tableaux" | "satML-tableaux" ->
          Ok Util.CDCL_Tableaux
        | "tableaux" | "Tableaux"
        | "tableaux-like" | "Tableaux-like" ->
          Ok Util.Tableaux
        | "tableaux-cdcl" | "Tableaux-CDCL"
        | "tableaux-CDCL" | "Tableaux-cdcl" ->
          Ok Util.Tableaux_CDCL
        | sat_solver ->
          Error ("Args parsing error: unkown SAT solver " ^ sat_solver)

      in
      Arg.(conv' (parse, Util.pp_sat_solver))
    in
    let default, sum_up = "CDCL-Tableaux", "satML" in
    let doc = Format.sprintf
        "Choose the SAT solver to use. Default value is %s (i.e. %s\
         solver). Possible options are %s."
        default sum_up
        (Arg.doc_alts ["CDCL"; "satML"; "CDCL-Tableaux";
                       "satML-Tableaux"; "Tableaux-CDCL"])
    in
    let docv = "SAT" in
    Arg.(value & opt sat_solver Util.CDCL_Tableaux &
         info ["sat-solver"] ~docv ~docs:s_sat ~doc)
  in

  let cdcl_tableaux_inst =
    let no_tableaux_cdcl_in_instantiation =
      let doc = "When satML is used, this disables the use of a tableaux-like \
                 method for instantiations with the CDCL solver." in
      Arg.(
        value & flag &
        info ["no-tableaux-cdcl-in-instantiation"]
          ~docs:s_sat ~doc)
    in
    Term.(const not $ no_tableaux_cdcl_in_instantiation)
  in

  let cdcl_tableaux_th =
    let no_tableaux_cdcl_in_theories =
      let doc = "When satML is used, this disables the use of a tableaux-like \
                 method for theories with the CDCL solver." in
      Arg.(
        value & flag &
        info ["no-tableaux-cdcl-in-theories"] ~docs:s_sat ~doc
      )
    in
    Term.(const not $ no_tableaux_cdcl_in_theories)
  in

  let strict_mode =
    let strict_mode_arg =
      let doc =
        "Enable strict mode (compliance with SMT-LIB standard)"
      in
      Arg.(value & flag & info ["strict"] ~doc ~docs:s_models)
    in
    Term.(const Options.set_strict_mode $ strict_mode_arg)
  in

  let set_sat_options =
    let set_sat_options sat_solver cdcl_tableaux_inst cdcl_tableaux_th () =
      begin match sat_solver with
        | Util.CDCL_Tableaux ->
          set_sat_solver sat_solver;
          set_cdcl_tableaux_inst cdcl_tableaux_inst;
          set_cdcl_tableaux_th cdcl_tableaux_th;
          Ok ()
        | Util.CDCL ->
          set_sat_solver sat_solver;
          set_cdcl_tableaux_inst false;
          set_cdcl_tableaux_th false;
          Ok ()
        | _ ->
          set_sat_solver sat_solver;
          set_cdcl_tableaux_inst false;
          set_cdcl_tableaux_th false;
          Ok ()
      end
    in
    let term =
      Term.(
        const set_sat_options $ sat_solver $ cdcl_tableaux_inst
        $ cdcl_tableaux_th $ strict_mode
      )
    in
    Term.term_result' term
  in

  let use_underscore =
    let doc = "Output \"_\" instead of fresh value in interpretation" in
    let deprecated =
      "this option will be removed as it does not produce a \
       SMTLIB-compliant output."
    in
    let docv = "VAL" in
    Arg.(value & flag & info
           ["interpretation-use-underscore";"use-underscore"]
           ~docv ~docs:s_models ~doc ~deprecated)
  in
  let objectives_in_interpretation =
    let doc = " inline pretty-printing of optimized expressions in the \
               model instead of a dedicated section '(objectives \
               ...)'. Be aware that a part of the model may be shrunk \
               or not accurate if some expressions to optimize are \
               unbounded." in
    Arg.(value & flag & info
           ["objectives-in-interpretation";"objectives-in-model";
            "obj-in-interpretation";"obj-in-model"] ~doc)
  in
  let unsat_core =
    let doc = "Experimental support for computing and printing unsat-cores." in
    Arg.(value & flag & info ["u"; "unsat-core"] ~doc ~docs)
  in
  let output_format =
    let doc =
      Format.sprintf
        "Control the output format of the solver, $(docv) must be %s.\
         The alt-ergo native format outputs Valid/Invalid/I don't know.\
         The smtlib2 format outputs unsat/sat/unknown.\
         If left unspecified, Alt-Ergo will use its heuristics to \
         determine the adequate output format according to the input format.\
         It must be noticed that not specifying an output \
         format will let Alt-Ergo set it according to the input file's \
         extension."
        (Arg.doc_alts [ "native"; "smtlib2" ])
    in
    let docv = "FMT" in
    Arg.(value & opt (some format_conv) None & info ["o"; "output"] ~docv ~doc)
  in

  let model_type =
    let doc =
      Format.sprintf
        "Control the output model type of the solver, $(docv) must be %s."
        (Arg.doc_alts [ "value"; "constraints" ])
    in
    let docv = "MTYP" in
    Arg.(
      value &
      opt (some model_type_conv) None &
      info ["mt"; "model-type"] ~docv ~doc ~docs:s_models
    )
  in

  let set_dump_models =
    Term.(const set_dump_models $ dump_models)
  in

  let set_dump_models_on =
    Term.(const Output.set_dump_models $ dump_models_on)
  in

  let set_verify_models =
    Term.(const set_verify_models $ verify_models)
  in

  let set_frontend =
    Term.(const set_frontend $ frontend)
  in

  Term.(ret (const mk_output_opt $
             interpretation $ use_underscore $
             objectives_in_interpretation $ unsat_core $
             output_format $ model_type $
             set_dump_models $ set_dump_models_on $ set_verify_models $
             set_sat_options $ set_frontend
            ))

let parse_profiling_opt =

  let docs = s_profiling in

  let cumulative_time_profiling =
    let doc =
      "Record the time spent in called functions in callers" in
    Arg.(value & flag & info ["cumulative-time-profiling"] ~docs ~doc) in

  let profiling =
    let doc =
      "Activate the profiling module with the given frequency. \
       Use Ctrl-C to switch between different views and \"Ctrl \
       + AltGr + \\\\ \" to exit." in
    let docv = "DELAY" in
    Arg.(value & opt (some float) None & info ["profiling"] ~docv ~docs ~doc) in

  let profiling_plugin =
    let doc = "Use the given profiling plugin." in
    let docv = "PGN" in
    Arg.(value & opt string (get_profiling_plugin ()) &
         info ["profiling-plugin"] ~docv ~docs ~doc) in

  Term.(ret (const mk_profiling_opt $
             cumulative_time_profiling $ profiling $
             profiling_plugin $ get_verbose_t
            ))

let parse_quantifiers_opt =

  let docs = s_quantifiers in

  let instantiation_heuristic =
    let doc = Format.sprintf
        "Change the instantiation heuristic. \
         $(docv) must be %s. By default %s is used for both sat solvers. \
         %s does one less phase of instantiation. \
         %s use all available ground terms in instantiation."
        (Arg.doc_alts ["normal"; "auto"; "greedy"])
        (Arg.doc_quote "auto")
        (Arg.doc_quote "normal")
        (Arg.doc_quote "greedy")
    in
    let docv = "VAL" in
    Arg.(value & opt instantiation_heuristic_conv IAuto &
         info ["instantiation-heuristic"] ~docv ~docs ~doc) in

  let instantiate_after_backjump =
    let doc =
      "Make a (normal) instantiation round after every backjump/backtrack." in
    Arg.(value & flag & info ["inst-after-bj"] ~docs ~doc) in

  let max_multi_triggers_size =
    let doc = "Maximum size of multi-triggers, i.e. the maximum number \
               of independent patterns in a multi-trigger." in
    let docv = "VAL" in
    Arg.(value & opt int (get_max_multi_triggers_size ()) &
         info ["max-multi-triggers-size"] ~docv ~docs ~doc) in

  let nb_triggers =
    let doc = "Maximum number of triggers used \
               (including regular and multi triggers)." in
    let docv = "VAL" in
    Arg.(value & opt int (get_nb_triggers ()) &
         info ["nb-triggers"] ~docv ~docs ~doc) in

  let no_ematching =
    let doc = "Disable matching modulo ground equalities." in
    Arg.(value & flag & info ["no-ematching"] ~docs ~doc) in

  let no_user_triggers =
    let doc =
      "Ignore user triggers, except for triggers of theories' axioms"; in
    Arg.(value & flag & info ["no-user-triggers"] ~docs ~doc) in

  let normalize_instances =
    let doc =
      "Normalize generated substitutions by matching w.r.t. the state of \
       the theory. This means that only terms that \
       are greater (w.r.t. depth) than the initial terms of the problem are \
       normalized." in
    Arg.(value & flag & info ["normalize-instances"] ~docs ~doc) in

  let triggers_var =
    let doc = "Allows variables as triggers." in
    Arg.(value & flag & info ["triggers-var"] ~docs ~doc) in

  Term.(ret (const mk_quantifiers_opt $ instantiation_heuristic $
             instantiate_after_backjump $ max_multi_triggers_size $
             nb_triggers $ no_ematching $ no_user_triggers $
             normalize_instances $ triggers_var
            ))

let parse_sat_opt =

  let docs = s_sat in

  let get_bottom_classes =
    let doc = "Show equivalence classes at each bottom of the sat." in
    Arg.(value & flag & info ["bottom-classes"] ~docs ~doc) in

  let disable_flat_formulas_simplification =
    let doc = "Disable facts simplifications in satML's flat formulas." in
    Arg.(value & flag &
         info ["disable-flat-formulas-simplification"] ~docs ~doc) in

  let enable_restarts =
    let doc =
      "For satML: enable restarts or not. Default behavior is 'false'." in
    Arg.(value & flag & info ["enable-restarts"] ~docs ~doc) in

  let no_arith_matching =
    let doc = "Disable (the weak form of) matching modulo linear arithmetic." in
    Arg.(value & flag & info ["no-arith-matching"] ~docs ~doc) in

  let no_backjumping =
    let doc = "Disable backjumping mechanism in the functional SAT solver." in
    Arg.(value & flag & info ["no-backjumping"] ~docs ~doc) in

  let no_backward =
    let doc =
      "Disable backward reasoning step (starting from the goal) done in \
       the default SAT solver before deciding." in
    Arg.(value & flag & info ["no-backward"] ~docs ~doc) in

  let no_decisions =
    let doc = "Disable decisions at the SAT level." in
    Arg.(value & flag & info ["no-decisions"] ~docs ~doc) in

  let no_decisions_on =
    let doc =
      "Disable decisions at the SAT level for the instances generated \
       from the given axioms. Arguments should be separated with a comma." in
    let docv = "[INST1; INST2; ...]" in
    Arg.(value & opt string "" &
         info ["no-decisions-on"] ~docv ~docs ~doc) in

  let no_minimal_bj =
    let doc = "Disable minimal backjumping in satML CDCL solver." in
    Arg.(value & flag & info ["no-minimal-bj"] ~docs ~doc) in

  let no_sat_learning =
    let doc =
      "Disable learning/caching of unit facts in the Default SAT. These \
       facts are used to improve bcp." in
    Arg.(value & flag & info ["no-sat-learning"] ~docs ~doc) in

  Term.(const mk_sat_opt $
        get_bottom_classes $ disable_flat_formulas_simplification $
        enable_restarts $ no_arith_matching $
        no_backjumping $ no_backward $ no_decisions $ no_decisions_on $
        no_minimal_bj $ no_sat_learning)

let parse_term_opt =

  let docs = s_term in

  let disable_ites =
    let doc = "Disable handling of ite(s) on terms in the backend." in
    Arg.(value & flag & info ["disable-ites"] ~docs ~doc) in

  let inline_lets =
    let doc =
      "Enable substitution of variables bounds by Let. The default \
       behavior is to only substitute variables that are bound to a \
       constant, or that appear at most once." in
    Arg.(value & flag & info ["inline-lets"] ~docs ~doc) in

  let rewriting =
    let doc = "Use rewriting instead of axiomatic approach." in
    Arg.(value & flag & info ["rwt"; "rewriting"] ~docs ~doc) in

  let no_term_like_pp =
    let doc = "Do not output semantic values as terms." in
    Arg.(value & flag & info ["no-term-like-pp"] ~docs ~doc) in

  Term.(ret (const mk_term_opt $
             disable_ites $ inline_lets $ rewriting $ no_term_like_pp
            ))

let parse_theory_opt =

  let docs = s_theory in

  let inequalities_plugin =
    let load_inequalities_plugin debug path =
      let debug = List.exists (List.exists (Debug.equal Debug.Fm)) debug in
      match path with
      | "" ->
        if debug then
          Printer.print_dbg
            "Using the 'FM module' for arithmetic inequalities";
        Ok ()
      | path ->
        try
          Config.load_plugin path;
          if debug then
            Printer.print_dbg
              "Using the 'inequalities' reasoner (FM module) %S" path;
          Ok ()
        with Errors.Error e ->
          Error (Format.asprintf "%a" Errors.report e)
    in
    let arg =
      let doc =
        "Use the given module to handle inequalities of linear arithmetic." in
      Arg.(value & opt string "" &
           info ["inequalities-plugin"] ~docs ~doc)
    in
    let term =
      Term.(const load_inequalities_plugin $ Debug.light_flag_term $ arg)
    in
    Term.term_result' term
  in

  let no_contracongru =
    let doc = "Disable contracongru." in
    Arg.(value & flag & info ["no-contracongru"] ~docs ~doc) in

  let no_fm =
    let doc = "Disable Fourier-Motzkin algorithm." in
    Arg.(value & flag & info ["no-fm"] ~docs ~doc) in

  let no_nla =
    let doc = "Disable non-linear arithmetic reasoning (i.e. non-linear \
               multplication, division and modulo on integers and rationals). \
               Non-linear multiplication remains AC." in
    Arg.(value & flag & info ["no-nla"] ~docs ~doc) in

  let no_tcp =
    let doc =
      "Deactivate Boolean Constant Propagation (BCP) modulo theories." in
    Arg.(value & flag & info ["no-tcp"] ~docs ~doc) in

  let no_theory =
    let doc = "Completely deactivate theory reasoning." in
    Arg.(value & flag & info ["no-theory"] ~docs ~doc) in

  let restricted =
    let doc =
      "Restrict set of decision procedures (equality, arithmetic and AC)." in
    Arg.(value & flag & info ["restricted"] ~docs ~doc) in

  let tighten_vars =
    let doc = "Compute the best bounds for arithmetic variables." in
    Arg.(value & flag & info ["tighten-vars"] ~docs ~doc) in

  let use_fpa =
    let doc = "Floating-point builtins are always enabled and this option has
      no effect anymore. It will be removed in a future version." in
    let deprecated = "this option is always enabled" in
    Arg.(value & flag & info ["use-fpa"] ~docs ~doc ~deprecated) in

  let theories =
    let theory_enum =
      Theories.all
      |> List.map (fun t -> Format.asprintf "%a" Theories.pp t, t)
    in
    let theory = Arg.enum theory_enum in
    let enable_theories =
      let doc =
        Format.asprintf "Enable builtin theory, multiple comma-separated values
        are supported. $(docv) must be %s."
          (Arg.doc_alts_enum theory_enum)
      in
      let docv = "THEORY" in
      Term.(const List.concat $
            Arg.(
              value
              & opt_all (list theory) []
              & info ["enable-theory"; "enable-theories"] ~docs ~doc ~docv
            ))
    and disable_theories =
      let doc =
        Format.asprintf "Disable builtin theory, multiple comma-separated
        values are supported. THEORY must be %s."
          (Arg.doc_alts_enum theory_enum)
      in
      let docv = "THEORY" in
      let disable_theories =
        Term.(const List.concat $
              Arg.(
                value
                & opt_all (list theory) []
                & info ["disable-theory"; "disable-theories"] ~docs ~doc ~docv
              ))
      in
      let disable_adts =
        let doc = "Disable Algebraic Datatypes theory. Deprecated alias for
        `--disable-theories adt`." in
        let deprecated = "use `--disable-theories ac` instead." in
        Arg.(value & flag & info ["disable-adts"] ~docs ~doc ~deprecated)
      in
      let no_ac =
        let doc = "Disable the AC theory of Associative and \
                   Commutative function symbols. Deprecated alias for
                  `--disable-theories ac`." in
        let deprecated = "use `--disable-theories ac` instead" in
        Arg.(value & flag & info ["no-ac"] ~docs ~doc ~deprecated)
      in
      let mk_disable_theories disable_theories disable_adts no_ac =
        let open Theories in
        (if disable_adts then [ ADT ] else []) @
        (if no_ac then [ AC ] else []) @
        disable_theories
      in
      Term.(const mk_disable_theories $ disable_theories $ disable_adts $ no_ac)
    in
    let preludes enable_theories disable_theories =
      let theories = Theories.default in
      let rec aux th en dis =
        match en, dis with
        | _ :: _, [] -> aux (List.rev_append en th) [] []
        | e :: _, d :: _ when e = d ->
          Fmt.error_msg "theory prelude '%a' cannot be both enabled and
          disabled" Theories.pp e
        | e :: en, d :: _ when e < d -> aux (e :: th) en dis
        | _ , d :: dis -> aux (List.filter ((<>) d) th) en dis
        | [], [] -> Ok th
      in
      aux
        theories
        (List.fast_sort compare enable_theories)
        (List.fast_sort compare disable_theories)
    in
    Term.(
      cli_parse_result (
        const preludes
        $ enable_theories
        $ disable_theories
      )
    )
  in

  Term.(ret (const mk_theory_opt $
             inequalities_plugin $ no_contracongru $
             no_fm $ no_nla $ no_tcp $ no_theory $ restricted $
             tighten_vars $ use_fpa $ theories
            )
       )

let parse_fmt_opt =
  let docs = s_fmt in
  let docv = "OUTPUT" in

  let regular_output =
    let doc =
      Format.sprintf
        "Set the regular output used by default to print the results,
          models and unsat cores. Possible values are %s."
        (Arg.doc_alts ["stdout"; "stderr"; "<filename>"])
    in
    Arg.(value & opt string "stdout" & info ["regular-output"] ~docs
           ~doc ~docv)
  in
  let diagnostic_output =
    let doc =
      Format.sprintf
        "Set the diagnostic output used by default to print error, debug and
         warning informations. Possible values are %s."
        (Arg.doc_alts ["stdout"; "stderr"; "<filename>"])
    in
    Arg.(value & opt string "stderr" & info ["diagnostic-output"] ~docs
           ~doc ~docv)
  in
  Term.(ret (const mk_output_channel_opt $ regular_output $ diagnostic_output))

let main =

  let file =
    let doc =
      "Source file. Must be suffixed by $(i,.ae), \
       ($(i,.mlw) and $(i,.why) are deprecated), \
       $(i,.smt2) or $(i,.psmt2)." in
    let i = Arg.(info [] ~docv:"FILE" ~doc) in
    Arg.(value & pos ~rev:true 0 (some file) None & i) in

  let doc = "Execute Alt-Ergo on the given file." in
  let exits = Cmd.Exit.defaults in
  let to_exit = Cmd.Exit.info ~doc:"on timeout errors" ~max:142 142 in
  let dft_errors = Cmd.Exit.info ~doc:"on default errors" ~max:1 1 in
  let exits = to_exit :: dft_errors :: exits in

  (* Specify the order in which the sections should appear
     Default behaviour gives an unpleasant result with
     non standard sections appearing before standard ones *)
  let man =
    [
      `S Manpage.s_options;
      `S s_execution;
      `S s_limit;
      `S s_internal;
      `S s_output;
      `S s_context;
      `S s_profiling;
      `S s_sat;
      `S s_quantifiers;
      `S s_term;
      `S s_theory;
      `S s_case_split;
      `S s_halt;
      `S s_fmt;
      `S s_models;
      `S s_debug;
      `P "These options are used to output debug info for the concerned \
          part of the solver.\
          They are $(b,not) used to check internal consistency.";
      `S Manpage.s_bugs;
      `P "You can open an issue on: \
          https://github.com/OCamlPro/alt-ergo/issues";
      `Pre "Or you can write to: \n   alt-ergo@ocamlpro.com";
      `S Manpage.s_authors;
      `Pre "CURRENT AUTHORS\n\
           \   Guillaume Bury\n\
           \   Basile Clément\n\
           \   Steven de Olivera\n\
           \   Hichem Rami Ait El Hara\n\
           \   Pierre Villemot";
      `Pre "PREVIOUS AUTHORS\n\
           \   Albin Coquereau\n\
           \   Mattias Roux";
      `Pre "ORIGINAL AUTHORS\n\
           \   Sylvain Conchon\n\
           \   Evelyne Contejean\n\
           \   Mohamed Iguernlala\n\
           \   Stephane Lescuyer\n\
           \   Alain Mebsout\n";
    ]
  in

  let term =
    Term.(ret (const mk_opts $
               file $
               parse_case_split_opt $ parse_context_opt $
               Debug.light_flag_term $ Debug.medium_flag_term $
               Debug.full_flag_term $ Rule.flag_term $ parse_execution_opt $
               parse_halt_opt $ parse_internal_opt $ parse_limit_opt $
               parse_profiling_opt $ parse_quantifiers_opt $ parse_sat_opt $
               parse_term_opt $ parse_output_opt $
               parse_theory_opt $ parse_fmt_opt
              ))
  in
  let info =
    Cmd.info "alt-ergo" ~version:Version._version ~doc ~exits ~man
  in
  Cmd.v info term

let parse_cmdline_arguments () =
  at_exit Options.Output.close_all;
  let r = Cmd.eval_value main in
  match r with
  | Ok `Ok true -> ()
  | Ok `Ok false -> raise (Exit_parse_command 0)
  | Ok `Version | Ok `Help -> exit 0
  | Error `Parse -> exit Cmd.Exit.cli_error
  | Error `Term -> exit Cmd.Exit.internal_error
  | Error `Exn -> exit Cmd.Exit.internal_error
