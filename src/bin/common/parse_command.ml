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

open AltErgoLib
open Options
open Cmdliner

exception Error of bool * string

(* Exception used to exit with corresponding retcode *)
exception Exit_parse_command of int

let model_parser = function
  | "none" -> Ok MNone
  | "default" -> Ok MDefault
  | "complete" -> Ok MComplete
  | "all" -> Ok MAll
  | s ->
    Error (`Msg ("Option --model does not accept the argument \"" ^ s))

let model_to_string = function
  | MNone -> "none"
  | MDefault -> "default"
  | MComplete -> "complete"
  | MAll -> "all"

let model_printer fmt model = Format.fprintf fmt "%s" (model_to_string model)

let model_conv = Arg.conv ~docv:"MDL" (model_parser, model_printer)

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
   "smtlib2", Smtlib2;
   "smt-lib2", Smtlib2;
   "why3", Why3]

let format_parser s =
  try
    Ok (List.assoc s formats_list)
  with
    Not_found ->
    Error (`Msg (Format.sprintf
                   "The format %s is not accepted as input/output" s))

let format_to_string = function
  | Native -> "native"
  | Smtlib2 -> "smtlib2"
  | Why3 -> "why3"
  | Unknown s -> Format.sprintf "Unknown %s" s

let format_printer fmt format =
  Format.fprintf fmt "%s" (format_to_string format)

let format_conv = Arg.conv ~docv:"FMT" (format_parser, format_printer)

type formatter = Stdout | Stderr | Other of string

let value_of_fmt = function
  | Stdout -> Format.std_formatter
  | Stderr -> Format.err_formatter
  | Other s ->
    let oc = open_out s in
    at_exit (fun () -> close_out oc);
    Format.formatter_of_out_channel oc

let formatter_parser = function
  | "stdout" -> Ok Stdout
  | "stderr" -> Ok Stderr
  | s -> Ok (Other s)

let formatter_to_string = function
  | Stdout -> "stdout"
  | Stderr -> "stderr"
  | Other s -> s

let formatter_printer fmt formatter =
  Format.fprintf fmt "%s" (formatter_to_string formatter)

let formatter_conv = Arg.conv ~docv:"FMT" (formatter_parser, formatter_printer)

type rule = RParsing | RTyping | RSat | RCC | RArith | RNone

let value_of_rule = function
  | RParsing -> 0
  | RTyping -> 1
  | RSat -> 2
  | RCC -> 3
  | RArith -> 4
  | RNone -> -1

let rule_parser = function
  | "parsing" -> Ok RParsing
  | "typing" -> Ok RTyping
  | "sat" -> Ok RSat
  | "cc" -> Ok RCC
  | "arith" -> Ok RArith
  | "none" -> Ok RNone
  | s ->
    Error (`Msg ("Option --rule does not accept the argument \"" ^ s))

let rule_to_string = function
  | RParsing -> "parsing"
  | RTyping -> "typing"
  | RSat -> "sat"
  | RCC -> "cc"
  | RArith -> "arith"
  | RNone -> "none"

let rule_printer fmt rule = Format.fprintf fmt "%s" (rule_to_string rule)

let rule_conv = Arg.conv ~docv:"MDL" (rule_parser, rule_printer)

let mk_dbg_opt_spl1 debug debug_ac debug_adt debug_arith debug_arrays
    debug_bitv debug_cc debug_combine debug_constr
  =
  set_debug debug;
  set_debug_ac debug_ac;
  set_debug_adt debug_adt;
  set_debug_arith debug_arith;
  set_debug_arrays debug_arrays;
  set_debug_bitv debug_bitv;
  set_debug_cc debug_cc;
  set_debug_combine debug_combine;
  set_debug_constr debug_constr;
  `Ok()

let mk_dbg_opt_spl2 debug_explanations debug_fm debug_fpa debug_gc
    debug_interpretation debug_ite debug_matching debug_sat
  =
  set_debug_explanations debug_explanations;
  set_debug_fm debug_fm;
  set_debug_fpa debug_fpa;
  set_debug_gc debug_gc;
  set_debug_interpretation debug_interpretation;
  set_debug_ite debug_ite;
  set_debug_matching debug_matching;
  set_debug_sat debug_sat;
  `Ok()

let mk_dbg_opt_spl3 debug_split debug_sum debug_triggers debug_types
    debug_typing debug_uf debug_unsat_core debug_use debug_warnings rule
  =
  let rule = value_of_rule rule in
  set_debug_split debug_split;
  set_debug_sum debug_sum;
  set_debug_triggers debug_triggers;
  set_debug_types debug_types;
  set_debug_typing debug_typing;
  set_debug_uf debug_uf;
  set_debug_unsat_core debug_unsat_core;
  set_debug_use debug_use;
  set_debug_warnings debug_warnings;
  set_rule rule;
  `Ok()

let mk_case_split_opt case_split_policy enable_adts_cs max_split
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

let mk_execution_opt frontend input_format parse_only parsers
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
  set_infer_input_format input_format;
  let input_format = match input_format with
    | None -> Native
    | Some fmt -> fmt
  in
  set_answers_with_loc answers_with_loc;
  set_output_with_colors output_with_colors;
  set_output_with_headers output_with_headers;
  set_output_with_formatting output_with_formatting;
  set_output_with_forced_flush output_with_forced_flush;
  set_input_format input_format;
  set_parse_only parse_only;
  set_parsers parsers;
  set_frontend frontend;
  set_type_only type_only;
  set_type_smt2 type_smt2;
  set_preludes preludes;
  `Ok()

let mk_internal_opt disable_weaks enable_assertions warning_as_error gc_policy
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
    let timelimit_interpretation = set_limit timelimit_interpretation 1. in
    set_age_bound age_bound;
    set_fm_cross_limit fm_cross_limit;
    set_timelimit_interpretation timelimit_interpretation;
    set_steps_bound steps_bound;
    set_timelimit timelimit;
    set_timelimit_per_goal timelimit_per_goal;
    `Ok()

let mk_output_opt interpretation model unsat_core output_format
  =
  set_infer_output_format output_format;
  let output_format = match output_format with
    | None -> Native
    | Some fmt -> fmt
  in
  set_interpretation interpretation;
  set_model model;
  set_unsat_core unsat_core;
  set_output_format output_format;
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
    no_minimal_bj no_sat_learning no_tableaux_cdcl_in_instantiation
    no_tableaux_cdcl_in_theories sat_plugin sat_solver
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

  let cdcl_tableaux_inst = not no_tableaux_cdcl_in_instantiation in
  let cdcl_tableaux_th = not no_tableaux_cdcl_in_theories in
  let res = match sat_solver with
    | "CDCL" | "satML" ->
      `Ok(Util.CDCL, false, false, false)
    | "CDCL-Tableaux" | "satML-Tableaux" | "CDCL-tableaux" | "satML-tableaux" ->
      `Ok(Util.CDCL_Tableaux, cdcl_tableaux_inst, cdcl_tableaux_th, false)
    | "tableaux" | "Tableaux" | "tableaux-like" | "Tableaux-like" ->
      `Ok(Util.Tableaux, false, false, false)
    | "tableaux-cdcl" | "Tableaux-CDCL" | "tableaux-CDCL" | "Tableaux-cdcl" ->
      `Ok(Util.Tableaux_CDCL, false, false, true)
    | _ -> `Error ("Args parsing error: unkown SAT solver " ^ sat_solver)
  in
  match res with
  | `Ok(sat_solver, cdcl_tableaux_inst, cdcl_tableaux_th, tableaux_cdcl) ->
    set_arith_matching arith_matching;
    set_bottom_classes get_bottom_classes;
    set_cdcl_tableaux_inst cdcl_tableaux_inst;
    set_cdcl_tableaux_th cdcl_tableaux_th;
    set_disable_flat_formulas_simplification
      disable_flat_formulas_simplification;
    set_enable_restarts enable_restarts;
    set_minimal_bj minimal_bj;
    set_no_backjumping no_backjumping;
    set_no_backward no_backward;
    set_no_decisions no_decisions;
    set_no_decisions_on no_decisions_on;
    set_no_sat_learning no_sat_learning;
    set_sat_plugin sat_plugin;
    set_sat_solver sat_solver;
    set_tableaux_cdcl tableaux_cdcl;
    `Ok()
  | `Error m -> `Error (false, m)

let mk_term_opt disable_ites inline_lets rewriting term_like_pp
  =
  set_rewriting rewriting;
  set_term_like_pp term_like_pp;
  set_disable_ites disable_ites;
  set_inline_lets inline_lets;
  `Ok()

let mk_theory_opt disable_adts inequalities_plugin no_ac no_contracongru
    no_fm no_nla no_tcp no_theory restricted tighten_vars use_fpa
  =
  set_no_ac no_ac;
  set_no_fm no_fm;
  set_no_nla no_nla;
  set_no_tcp no_tcp;
  set_no_theory no_theory;
  set_use_fpa use_fpa;
  set_inequalities_plugin inequalities_plugin;
  set_restricted restricted;
  set_disable_adts disable_adts;
  set_tighten_vars tighten_vars;
  set_no_contracongru no_contracongru;
  `Ok()

let halt_opt version_info where =
  let handle_where w =
    let res = match w with
      | "lib" -> `Ok Config.libdir
      | "plugins" -> `Ok Config.pluginsdir
      | "preludes" -> `Ok Config.preludesdir
      | "data" -> `Ok Config.datadir
      | "man" -> `Ok Config.mandir
      | _ -> `Error
               ("Option --where does not accept the argument \"" ^ w ^
                "\"\nAccepted options are lib, plugins, preludes, data or man")
    in
    match res with
    | `Ok path -> Printer.print_std "%s@." path
    | `Error m -> raise (Error (false, m))
  in
  let handle_version_info vi =
    if vi then (
      Printer.print_std
        "@[<v 0>Version          = %s@,\
         Release date     = %s@,\
         Release commit   = %s@]@."
        Version._version
        Version._release_date
        Version._release_commit;
    )
  in
  try
    match where with
    | Some w -> handle_where w; `Ok true
    | None -> if version_info then (handle_version_info version_info; `Ok true)
      else `Ok false
  with Failure f -> `Error (false, f)
     | Error (b, m) -> `Error (b, m)

let mk_opts file () () () () () () halt_opt (gc) () () () () () () () ()
  =

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

let mk_fmt_opt std_fmt err_fmt
  =
  set_std_fmt (value_of_fmt std_fmt);
  set_err_fmt (value_of_fmt err_fmt);
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

(* Parsers *)

let parse_dbg_opt_spl1 =

  let docs = s_debug in

  let debug =
    let doc = "Set the debugging flag." in
    Arg.(value & flag & info ["d"; "debug"] ~doc) in

  let debug_ac =
    let doc = "Set the debugging flag of ac." in
    Arg.(value & flag & info ["dac"] ~docs ~doc) in

  let debug_adt =
    let doc = "Set the debugging flag of ADTs." in
    Arg.(value & flag & info ["dadt"] ~docs ~doc) in

  let debug_arith =
    let doc = "Set the debugging flag of Arith (without fm)." in
    Arg.(value & flag & info ["darith"] ~docs ~doc) in

  let debug_arrays =
    let doc = "Set the debugging flag of arrays." in
    Arg.(value & flag & info ["darrays"] ~docs ~doc) in

  let debug_bitv =
    let doc = "Set the debugging flag of bitv." in
    Arg.(value & flag & info ["dbitv"] ~docs ~doc) in

  let debug_cc =
    let doc = "Set the debugging flag of cc." in
    Arg.(value & flag & info ["dcc"] ~docs ~doc) in

  let debug_combine =
    let doc = "Set the debugging flag of combine." in
    Arg.(value & flag & info ["dcombine"] ~docs ~doc) in

  let debug_constr =
    let doc = "Set the debugging flag of constructors." in
    Arg.(value & flag & info ["dconstr"] ~docs ~doc) in

  Term.(ret (const mk_dbg_opt_spl1 $
             debug $
             debug_ac $
             debug_adt $
             debug_arith $
             debug_arrays $
             debug_bitv $
             debug_cc $
             debug_combine $
             debug_constr
            ))

let parse_dbg_opt_spl2 =

  let docs = s_debug in

  let debug_explanations =
    let doc = "Set the debugging flag of explanations." in
    Arg.(value & flag & info ["dexplanations"] ~docs ~doc) in

  let debug_fm =
    let doc = "Set the debugging flag of inequalities." in
    Arg.(value & flag & info ["dfm"] ~docs ~doc) in

  let debug_fpa =
    let doc = "Set the debugging flag of floating-point." in
    Arg.(value & opt int (get_debug_fpa ()) & info ["dfpa"] ~docs ~doc) in

  let debug_gc =
    let doc = "Prints some debug info about the GC's activity." in
    Arg.(value & flag & info ["dgc"] ~docs ~doc) in

  let debug_interpretation =
    let doc = "Set debug flag for interpretation generatation." in
    Arg.(value & flag & info ["debug-interpretation"] ~docs ~doc) in

  let debug_ite =
    let doc = "Set the debugging flag of ite." in
    Arg.(value & flag & info ["dite"] ~docs ~doc) in

  let debug_matching =
    let doc = "Set the debugging flag \
               of E-matching (0=disabled, 1=light, 2=full)." in
    let docv = "FLAG" in
    Arg.(value & opt int (get_debug_matching ()) &
         info ["dmatching"] ~docv ~docs ~doc) in

  let debug_sat =
    let doc = "Set the debugging flag of sat." in
    Arg.(value & flag & info ["dsat"] ~docs ~doc) in

  Term.(ret (const mk_dbg_opt_spl2 $

             debug_explanations $
             debug_fm $
             debug_fpa $
             debug_gc $
             debug_interpretation $
             debug_ite $
             debug_matching $
             debug_sat
            ))

let parse_dbg_opt_spl3 =

  let docs = s_debug in

  let debug_split =
    let doc = "Set the debugging flag of case-split analysis." in
    Arg.(value & flag & info ["dsplit"] ~docs ~doc) in

  let debug_sum =
    let doc = "Set the debugging flag of Sum." in
    Arg.(value & flag & info ["dsum"] ~docs ~doc) in

  let debug_triggers =
    let doc = "Set the debugging flag of triggers." in
    Arg.(value & flag & info ["dtriggers"] ~docs ~doc) in

  let debug_types =
    let doc = "Set the debugging flag of types." in
    Arg.(value & flag & info ["dtypes"] ~docs ~doc) in

  let debug_typing =
    let doc = "Set the debugging flag of typing." in
    Arg.(value & flag & info ["dtyping"] ~docs ~doc) in

  let debug_uf =
    let doc = "Set the debugging flag of uf." in
    Arg.(value & flag & info ["duf"] ~docs ~doc) in

  let debug_unsat_core =
    let doc = "Replay unsat-cores produced by $(b,--unsat-core). \
               The option implies $(b,--unsat-core)." in
    Arg.(value & flag & info ["debug-unsat-core"] ~docs ~doc) in

  let debug_use =
    let doc = "Set the debugging flag of use." in
    Arg.(value & flag & info ["duse"] ~docs ~doc) in

  let debug_warnings =
    let doc = "Set the debugging flag of warnings." in
    Arg.(value & flag & info ["dwarnings"] ~docs ~doc) in

  let rule =
    let doc =
      "$(docv) = parsing|typing|sat|cc|arith, output rule used on stderr." in
    let docv = "TR" in
    Arg.(value & opt rule_conv RNone & info ["rule"] ~docv ~docs ~doc) in

  Term.(ret (const mk_dbg_opt_spl3 $

             debug_split $
             debug_sum $
             debug_triggers $
             debug_types $
             debug_typing $
             debug_uf $
             debug_unsat_core $
             debug_use $
             debug_warnings $
             rule
            ))

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

  let max_split =
    let dv = Numbers.Q.to_string (get_max_split ()) in
    let doc =
      Format.sprintf "Maximum size of case-split." in
    let docv = "VAL" in
    Arg.(value & opt string dv & info ["max-split"] ~docv ~docs ~doc) in

  Term.(ret (const mk_case_split_opt $
             case_split_policy $ enable_adts_cs $ max_split))

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

  let frontend =
    let doc = "Select the parsing and typing frontend." in
    let docv = "FTD" in
    Arg.(value & opt string (get_frontend ()) &
         info ["frontend"] ~docv ~docs ~doc) in

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
    let doc = "Register a new parser for Alt-Ergo." in
    Arg.(value & opt_all string (get_parsers ()) &
         info ["add-parser"] ~docs ~doc) in

  let preludes =
    let doc =
      "Add a file that will be loaded as a prelude. The command is \
       cumulative, and the order of successive preludes is preserved." in
    Arg.(value & opt_all string (get_preludes ()) &
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
             frontend $ input_format $ parse_only $ parsers $ preludes $
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
         %s." (Arg.doc_alts ["lib"; "plugins"; "preludes"; "data"; "man"]) in
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

  let gc_policy =
    let doc =
      "Set the gc policy allocation. 0 = next-fit policy, 1 = \
       first-fit policy, 2 = best-fit policy. See the Gc module \
       of the OCaml distribution for more informations." in
    let docv = "PLCY" in
    Arg.(value & opt int 0 & info ["gc-policy"] ~docv ~docs ~doc) in

  Term.(ret (const mk_internal_opt $
             disable_weaks $ enable_assertions $ warning_as_error $ gc_policy
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

  let interpretation =
    let doc =
      "Experimental support for counter-example generation. Possible \
       values are 1, 2, or 3 to compute an interpretation before returning \
       Unknown, before instantiation (1), or before every decision (2) or \
       instantiation (3). A negative value (-1, -2, or -3) will disable \
       interpretation display. Note that $(b, --max-split) limitation will \
       be ignored in model generation phase." in
    let docv = "VAL" in
    Arg.(value & opt int (get_interpretation ()) &
         info ["interpretation"] ~docv ~docs ~doc) in

  let model =
    let doc = Format.sprintf
        "Experimental support for models on labeled terms. \
         $(docv) must be %s. %s shows a complete model and %s shows \
         all models."
        (Arg.doc_alts ["none"; "default"; "complete"; "all"])
        (Arg.doc_quote "complete") (Arg.doc_quote "all") in
    let docv = "VAL" in
    Arg.(value & opt model_conv MNone & info ["m"; "model"] ~docv ~doc) in

  let unsat_core =
    let doc = "Experimental support for computing and printing unsat-cores." in
    Arg.(value & flag & info ["u"; "unsat-core"] ~doc) in

  let output_format =
    let doc =
      Format.sprintf
        "Control the output format of the solver, $(docv) must be %s.\
         The alt-ergo native format outputs Valid/Invalid/I don't know.\
         The smtlib format outputs unsat/sat/unknown.\
         If left unspecified, Alt-Ergo will use its heuristics to \
         determine the adequate output format according to the input format.\
         It must be noticed that not specifying an output \
         format will let Alt-Ergo set it according to the input file's \
         extension."
        (Arg.doc_alts [ "native"; "smtlib" ])
    in
    let docv = "FMT" in
    Arg.(value & opt (some format_conv) None & info ["o"; "output"] ~docv ~doc)
  in

  Term.(ret (const mk_output_opt $
             interpretation $ model $ unsat_core $ output_format
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

  let get_verbose =
    let doc = "Set the verbose mode." in
    Arg.(value & flag & info ["v"; "verbose"] ~doc) in

  Term.(ret (const mk_profiling_opt $
             cumulative_time_profiling $ profiling $
             profiling_plugin $ get_verbose
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

  let no_tableaux_cdcl_in_instantiation =
    let doc = "When satML is used, this disables the use of a tableaux-like\
               method for instantiations with the CDCL solver." in
    Arg.(value & flag &
         info ["no-tableaux-cdcl-in-instantiation"] ~docs ~doc) in

  let no_tableaux_cdcl_in_theories =
    let doc = "When satML is used, this disables the use of a tableaux-like\
               method for theories with the CDCL solver." in
    Arg.(value & flag & info ["no-tableaux-cdcl-in-theories"] ~docs ~doc) in

  let sat_plugin =
    let doc =
      "Use the given SAT-solver instead of the default DFS-based SAT solver." in
    Arg.(value & opt string (get_sat_plugin ()) &
         info ["sat-plugin"] ~docs ~doc) in

  let sat_solver =
    let doc = Format.sprintf
        "Choose the SAT solver to use. Default value is CDCL (i.e. satML \
         solver). Possible options are %s."
        (Arg.doc_alts ["CDCL"; "satML"; "CDCL-Tableaux";
                       "satML-Tableaux"; "Tableaux-CDCL"])
    in
    let docv = "SAT" in
    Arg.(value & opt string "CDCL-Tableaux" &
         info ["sat-solver"] ~docv ~docs ~doc) in

  Term.(ret (const mk_sat_opt $
             get_bottom_classes $ disable_flat_formulas_simplification $
             enable_restarts $ no_arith_matching $
             no_backjumping $ no_backward $ no_decisions $ no_decisions_on $
             no_minimal_bj $ no_sat_learning $
             no_tableaux_cdcl_in_instantiation $
             no_tableaux_cdcl_in_theories $ sat_plugin $ sat_solver
            ))

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

  let term_like_pp =
    let doc = "Output semantic values as terms." in
    Arg.(value & flag & info ["term-like-pp"] ~docs ~doc) in

  Term.(ret (const mk_term_opt $
             disable_ites $ inline_lets $ rewriting $ term_like_pp
            ))

let parse_theory_opt =

  let docs = s_theory in

  let disable_adts =
    let doc = "Disable Algebraic Datatypes theory." in
    Arg.(value & flag & info ["disable-adts"] ~docs ~doc) in

  let inequalities_plugin =
    let doc =
      "Use the given module to handle inequalities of linear arithmetic." in
    Arg.(value & opt string (get_inequalities_plugin ()) &
         info ["inequalities-plugin"] ~docs ~doc) in

  let no_ac =
    let doc = "Disable the AC theory of Associative and \
               Commutative function symbols." in
    Arg.(value & flag & info ["no-ac"] ~docs ~doc) in

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
    let doc = "Enable support for floating-point arithmetic." in
    Arg.(value & flag & info ["use-fpa"] ~docs ~doc) in

  Term.(ret (const mk_theory_opt $
             disable_adts $ inequalities_plugin $ no_ac $ no_contracongru $
             no_fm $ no_nla $ no_tcp $ no_theory $ restricted $
             tighten_vars $ use_fpa
            )
       )

let parse_fmt_opt =

  let docs = s_fmt in

  let std_formatter =
    let doc = Format.sprintf
        "Set the standard formatter used by default to output the results,
    models and unsat cores. Possible values are %s."
        (Arg.doc_alts ["stdout"; "stderr"; "<filename>"]) in
    Arg.(value & opt formatter_conv Stdout & info ["std-formatter"] ~docs ~doc)
  in

  let err_formatter =
    let doc = Format.sprintf
        "Set the error formatter used by default to output error, debug and
         warning informations. Possible values are %s."
        (Arg.doc_alts ["stdout"; "stderr"; "<filename>"]) in
    Arg.(value & opt formatter_conv Stderr & info ["err-formatter"] ~docs ~doc)
  in

  Term.(ret (const mk_fmt_opt $
             std_formatter $ err_formatter
            ))

let main =

  let file =
    let doc =
      "Source file. Must be suffixed by $(i,.ae), \
       ($(i,.mlw) and $(i,.why) are depreciated, \
       $(i,.smt2) or $(i,.psmt2)." in
    let i = Arg.(info [] ~docv:"FILE" ~doc) in
    Arg.(value & pos ~rev:true 0 (some string) None & i) in

  let doc = "Execute Alt-Ergo on the given file." in
  let exits = Term.default_exits in
  let to_exit = Term.(exit_info ~doc:"on timeout errors" ~max:142 142) in
  let dft_errors = Term.(exit_info ~doc:"on default errors" ~max:1 1) in
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
           \   Sylvain Conchon\n\
           \   Albin Coquereau\n\
           \   Guillaume Bury\n\
           \   Mattias Roux";

      `Pre "ORIGINAL AUTHORS\n\
           \   Sylvain Conchon\n\
           \   Evelyne Contejean\n\
           \   Mohamed Iguernlala\n\
           \   Stephane Lescuyer\n\
           \   Alain Mebsout\n";
    ]
  in

  Term.(ret (const mk_opts $
             file $
             parse_case_split_opt $ parse_context_opt $
             parse_dbg_opt_spl1 $ parse_dbg_opt_spl2 $ parse_dbg_opt_spl3 $
             parse_execution_opt $ parse_halt_opt $ parse_internal_opt $
             parse_limit_opt $ parse_output_opt $ parse_profiling_opt $
             parse_quantifiers_opt $ parse_sat_opt $ parse_term_opt $
             parse_theory_opt $ parse_fmt_opt
            )),
  Term.info "alt-ergo" ~version:Version._version ~doc ~exits ~man

let parse_cmdline_arguments () =
  let r = Cmdliner.Term.(eval main) in
  match r with
  | `Ok false -> raise (Exit_parse_command 0)
  | `Ok true -> ()
  | e -> exit @@ Term.(exit_status_of_result e)
