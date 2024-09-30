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

module Output = struct
  type t =
    | Stdout
    | Stderr
    | Channel of string * out_channel * Format.formatter
    | Fmt of Format.formatter
    | Invalid

  let to_string = function
    | Stdout -> "stdout"
    | Stderr -> "stderr"
    | Channel (fname, _, _) -> fname
    | Fmt _ -> "custom formatter"
    | Invalid -> "invalid"

  let of_formatter fmt = Fmt fmt

  let to_formatter = function
    | Stdout -> Format.std_formatter
    | Stderr -> Format.err_formatter
    | Channel (_, _, fmt) -> fmt
    | Fmt fmt -> fmt
    | Invalid -> assert false

  let create_channel = function
    | "stdout" -> Stdout
    | "stderr" -> Stderr
    | str ->
      let cout = open_out str in
      let fmt = Format.formatter_of_out_channel cout in
      Channel (str, cout, fmt)

  let regular_output = ref Stdout
  let diagnostic_output = ref Stderr
  let dump_models_output = ref Stderr

  let all_channels = [
    regular_output;
    diagnostic_output;
    dump_models_output;
  ]

  let close o =
    match o with
    | Stdout | Stderr | Fmt _ ->
      Format.pp_print_flush (to_formatter o) ();
    | Channel (_, cout, _) ->
      Format.pp_print_flush (to_formatter o) ();
      close_out cout
    | Invalid -> ()

  let set_output output o =
    close !output;
    output := o

  let close_all () = List.iter (fun o -> set_output o Invalid) all_channels

  let set_regular o = set_output regular_output o
  let set_diagnostic o = set_output diagnostic_output o
  let set_dump_models o = set_output dump_models_output o

  let get_fmt_regular () = to_formatter !regular_output
  let get_fmt_diagnostic () = to_formatter !diagnostic_output
  let get_fmt_models () = to_formatter !dump_models_output
end

module Sources = struct
  let constr = Logs.Src.create ~doc:"Constr" "AltErgoLib.constr"
  let fm = Logs.Src.create ~doc:"fm" "AltErgoLib.fm"
  let fpa = Logs.Src.create ~doc:"fpa" "AltErgoLib.fpa"
  let interpretation =
    Logs.Src.create ~doc:"Interpretation" "AltErgoLib.Interpretation"
  let model = Logs.Src.create ~doc:"Model" "AltErgoLib.Model"
  let optimize = Logs.Src.create ~doc:"Optimize" "AltErgoLib.Optimize"
  let split = Logs.Src.create ~doc:"Split" "AltErgoLib.Split"
  let triggers = Logs.Src.create ~doc:"Triggers" "AltErgoLib.Triggers"
  let types = Logs.Src.create ~doc:"Types" "AltErgoLib.Types"
  let typing = Logs.Src.create ~doc:"Typing" "AltErgoLib.Typing"
  let unsat_core = Logs.Src.create ~doc:"Unsat_core" "AltErgoLib.Unsat_core"
end

(* Declaration of all the options as refs with default values *)

type instantiation_heuristic = INormal | IAuto | IGreedy
type interpretation = INone | IFirst | IEvery | ILast

(* As in Dolmen *)
type smtlib2_version = [ `Latest | `V2_6 | `Poly ]

type input_format =
  | Native
  | Smtlib2 of smtlib2_version
  | Why3
  (* | SZS *)
  | Unknown of string
type output_format = input_format

type model_type = Value | Constraints

let match_extension e =
  match e with
  | ".ae" -> Native
  | ".smt2" -> Smtlib2 `Latest
  | ".psmt2" -> Smtlib2 `Poly
  | ".why" | ".mlw" -> Why3
  (* | ".szs" -> SZS *)
  | s -> Unknown s

type known_status =
    Status_Sat | Status_Unsat | Status_Unknown | Status_Undefined of string

let match_known_status s =
  match s with
  | "sat" -> Status_Sat
  | "unsat" -> Status_Unsat
  | "unknown" -> Status_Unknown
  | s -> Status_Undefined s

(* We don't want to handle functions with more than 10 arguments so
   we need to split the debug options to gather them in the end.
   Problems with this way of doing is the options in each "group" are sorted
   alphabetically before we split the corresponding group. Adding a new one may
   break the sorting which is why each group contains 7/8/9 options as of now
   to allow the adding of new ones in the right group
*)

let debug = ref false
let debug_ac = ref false
let debug_adt = ref false
let debug_arith = ref false
let debug_arrays = ref false
let debug_bitv = ref false
let debug_cc = ref false
let debug_combine = ref false
let debug_constr = ref false
let debug_explanations = ref false
let debug_fm = ref false
let debug_intervals = ref false
let debug_fpa = ref 0
let debug_gc = ref false
let debug_interpretation = ref false
let debug_ite = ref false
let debug_matching = ref 0
let debug_sat = ref false
let debug_split = ref false
let debug_triggers = ref false
let debug_types = ref false
let debug_uf = ref false
let debug_unsat_core = ref false
let debug_use = ref false
let debug_warnings = ref false
let debug_commands = ref false
let debug_optimize = ref false
let rule = ref (-1)

let set_debug b = debug := b
let set_debug_ac b = debug_ac := b
let set_debug_adt b = debug_adt := b
let set_debug_arith b = debug_arith := b
let set_debug_arrays b = debug_arrays := b
let set_debug_bitv b = debug_bitv := b
let set_debug_cc b = debug_cc := b
let set_debug_combine b = debug_combine := b
let set_debug_constr b = debug_constr := b
let set_debug_explanations b = debug_explanations := b
let set_debug_fm b = debug_fm := b
let set_debug_intervals b = debug_intervals := b
let set_debug_fpa i = debug_fpa := i
let set_debug_gc b = debug_gc := b
let set_debug_interpretation b = debug_interpretation := b
let set_debug_ite b = debug_ite := b
let set_debug_matching i = debug_matching := i
let set_debug_sat b = debug_sat := b
let set_debug_split b = debug_split := b
let set_debug_triggers b = debug_triggers := b
let set_debug_types b = debug_types := b
let set_debug_uf b = debug_uf := b
let set_debug_unsat_core b = debug_unsat_core := b
let set_debug_use b = debug_use := b
let set_debug_warnings b = debug_warnings := b
let set_debug_commands b = debug_commands := b
let set_debug_optimize b = debug_optimize := b
let set_rule b = rule := b

let get_debug () = !debug
let get_debug_ac () = !debug_ac
let get_debug_adt () = !debug_adt
let get_debug_arith () = !debug_arith
let get_debug_arrays () = !debug_arrays
let get_debug_bitv () = !debug_bitv
let get_debug_cc () = !debug_cc
let get_debug_combine () = !debug_combine
let get_debug_constr () = !debug_constr
let get_debug_explanations () = !debug_explanations
let get_debug_fm () = !debug_fm
let get_debug_intervals () = !debug_intervals
let get_debug_fpa () = !debug_fpa
let get_debug_gc () = !debug_gc
let get_debug_interpretation () = !debug_interpretation
let get_debug_ite () = !debug_ite
let get_debug_matching () = !debug_matching
let get_debug_sat () = !debug_sat
let get_debug_split () = !debug_split
let get_debug_triggers () = !debug_triggers
let get_debug_types () = !debug_types
let get_debug_uf () = !debug_uf
let get_debug_unsat_core () = !debug_unsat_core
let get_debug_use () = !debug_use
let get_debug_warnings () = !debug_warnings
let get_debug_commands () = !debug_commands
let get_debug_optimize () = !debug_optimize
let get_rule () = !rule

(** Case split options *)

let case_split_policy = ref Util.AfterTheoryAssume
let enable_adts_cs = ref false
let enable_sat_cs = ref false
let max_split = ref (Numbers.Q.from_int 1000000)

(* Case split setters *)

let set_case_split_policy p = case_split_policy := p
let set_enable_adts_cs b = enable_adts_cs := b
let set_enable_sat_cs b = enable_sat_cs := b
let set_max_split n = max_split := n

(* Case split getters *)

let get_case_split_policy () = !case_split_policy
let get_enable_adts_cs () = !enable_adts_cs
let get_enable_sat_cs () = !enable_sat_cs
let get_max_split () = !max_split

(** Context options *)

let replay = ref false
let replay_all_used_context = ref false
let replay_used_context = ref false
let save_used_context = ref false

let set_replay b = replay := b
let set_replay_all_used_context b = replay_all_used_context := b
let set_replay_used_context b = replay_used_context := b
let set_save_used_context b = save_used_context := b

let get_replay () = !replay
let get_replay_used_context () = !replay_used_context
let get_replay_all_used_context () = !replay_all_used_context
let get_save_used_context () = !save_used_context

(** Execution options *)

let answers_with_loc = ref true
let output_with_colors = ref false
let output_with_headers = ref true
let output_with_formatting = ref true
let output_with_forced_flush = ref true
let input_format = ref None
let parse_only = ref false
let preludes = ref []
let theory_preludes = ref Theories.default_preludes
let type_only = ref false
let type_smt2 = ref false

let set_answers_with_loc b = answers_with_loc := b
let set_output_with_colors b = output_with_colors := b
let set_output_with_headers b = output_with_headers := b
let set_output_with_formatting b = output_with_formatting := b
let set_output_with_forced_flush b = output_with_forced_flush := b
let set_input_format f = input_format := f
let set_parse_only b = parse_only := b
let set_preludes p = preludes := p

let set_theory_preludes t = theory_preludes := t
let set_type_only b = type_only := b
let set_type_smt2 b = type_smt2 := b

let get_answers_with_locs () = !answers_with_loc
let get_output_with_colors () = !output_with_colors
let get_output_with_headers () = !output_with_headers
let get_output_with_formatting () = !output_with_formatting
let get_output_with_forced_flush () = !output_with_forced_flush
let get_input_format () = !input_format
let get_parse_only () = !parse_only
let get_preludes () = !preludes
let get_theory_preludes () = !theory_preludes
let get_type_only () = !type_only
let get_type_smt2 () = !type_smt2

(** Internal options *)

let disable_weaks = ref false
let enable_assertions = ref false
let warning_as_error = ref false
let exit_on_error = ref true

let set_disable_weaks b = disable_weaks := b
let set_enable_assertions b = enable_assertions := b
let set_warning_as_error b = warning_as_error := b
let set_exit_on_error b = exit_on_error := b

let get_disable_weaks () = !disable_weaks
let get_enable_assertions () = !enable_assertions
let get_warning_as_error () = !warning_as_error
let get_exit_on_error () = !exit_on_error

(** Limit options *)

let age_bound = ref 50
let fm_cross_limit = ref (Numbers.Q.from_int 10_000)
let steps_bound = ref (-1)
let timelimit = ref 0.
(* let timelimit_interpretation = ref (if Sys.win32 then 0. else 1.) *)
let timelimit_interpretation = ref 0.
let timelimit_per_goal = ref false

let set_age_bound i = age_bound := i
let set_fm_cross_limit l = fm_cross_limit := l
let set_steps_bound i = steps_bound := i
let set_timelimit l = timelimit := l
let set_timelimit_interpretation l = timelimit_interpretation := l
let set_timelimit_per_goal l = timelimit_per_goal := l

let get_age_bound () = !age_bound
let get_fm_cross_limit () = !fm_cross_limit
let get_steps_bound () = !steps_bound
let get_timelimit () = !timelimit
let get_timelimit_interpretation () = !timelimit_interpretation
let get_timelimit_per_goal () = !timelimit_per_goal

(** Output options *)

let interpretation = ref INone
let strict_mode = ref false
let dump_models = ref false
let interpretation_use_underscore = ref false
let objectives_in_interpretation = ref false
let output_format = ref Native
let model_type = ref Value
let infer_output_format = ref true
let unsat_core = ref false

let set_interpretation b = interpretation := b
let set_strict_mode b = strict_mode := b
let set_dump_models b = dump_models := b
let set_interpretation_use_underscore b = interpretation_use_underscore := b
let set_objectives_in_interpretation b = objectives_in_interpretation := b
let set_output_format b = output_format := b
let set_model_type t = model_type := t
let set_infer_output_format b = infer_output_format := b
let set_unsat_core b = unsat_core := b

let equal_mode a b =
  match a, b with
  | INone, INone -> true
  | INone, _ | _, INone -> false
  | IFirst, IFirst -> true
  | IFirst, _ | _, IFirst -> false
  | IEvery, IEvery -> true
  | IEvery, _ | _, IEvery -> false
  | ILast, ILast -> true

let equal_mode_type a b =
  match a, b with
  | Constraints, Constraints -> true
  | Constraints, _ | _, Constraints -> false
  | Value, Value -> true

let get_interpretation () = not @@ equal_mode !interpretation INone
let get_strict_mode () = !strict_mode
let get_dump_models () = !dump_models
let get_first_interpretation () = equal_mode !interpretation IFirst
let get_every_interpretation () = equal_mode !interpretation IEvery
let get_last_interpretation () = equal_mode !interpretation ILast
let get_interpretation_use_underscore () = !interpretation_use_underscore
let get_objectives_in_interpretation () = !objectives_in_interpretation
let get_output_format () = !output_format
let get_output_smtlib () =
  match !output_format with
  | Smtlib2 _ -> true
  | _ -> false
let get_model_type () = !model_type
let get_model_type_constraints () = equal_mode_type !model_type Constraints
let get_infer_output_format () = !infer_output_format
let get_unsat_core () = !unsat_core || !save_used_context || !debug_unsat_core

(** Profiling options *)

let cumulative_time_profiling = ref false
let profiling = ref false
let profiling_period = ref 0.
let profiling_plugin = ref ""
let verbose = ref false

let set_cumulative_time_profiling b = cumulative_time_profiling := b
let set_profiling b f =
  profiling := b;
  profiling_period := if b then f else 0.
let set_profiling_period p = profiling_period := p
let set_profiling_plugin p = profiling_plugin := p
let set_verbose b = verbose := b

let get_cumulative_time_profiling () = !cumulative_time_profiling
let get_profiling () = !profiling
let get_profiling_period () = !profiling_period
let get_profiling_plugin () = !profiling_plugin
let get_verbose () = !verbose

(** Quantifiers options *)


let instantiation_heuristic = ref IAuto
let instantiate_after_backjump = ref false
let max_multi_triggers_size = ref 4
let nb_triggers = ref 2
let no_ematching = ref false
let no_user_triggers = ref false
let normalize_instances = ref false
let triggers_var = ref false


let set_instantiation_heuristic i = instantiation_heuristic := i
let set_instantiate_after_backjump b = instantiate_after_backjump := b
let set_max_multi_triggers_size b = max_multi_triggers_size := b
let set_nb_triggers b = nb_triggers := b
let set_no_ematching b = no_ematching := b
let set_no_user_triggers b = no_user_triggers := b
let set_normalize_instances b = normalize_instances := b
let set_triggers_var b = triggers_var := b

let equal_heuristic a b =
  match a, b with
  | IGreedy, IGreedy | INormal, INormal | IAuto, IAuto -> true
  | IGreedy, (INormal | IAuto)
  | INormal, (IGreedy | IAuto)
  | IAuto, (IGreedy | INormal) -> false

let get_instantiation_heuristic () = !instantiation_heuristic
let get_greedy () = equal_heuristic !instantiation_heuristic IGreedy
let get_instantiate_after_backjump () = !instantiate_after_backjump
let get_max_multi_triggers_size () = !max_multi_triggers_size
let get_nb_triggers () = !nb_triggers
let get_no_ematching () = !no_ematching
let get_no_user_triggers () = !no_user_triggers
let get_normalize_instances () = !normalize_instances
let get_triggers_var () = !triggers_var

(** Sat options *)

let arith_matching = ref false
let bottom_classes = ref false
let cdcl_tableaux_inst = ref false
let cdcl_tableaux_th = ref false
let disable_flat_formulas_simplification = ref false
let enable_restarts = ref false
let minimal_bj = ref false
let no_backjumping = ref false
let no_backward = ref false
let no_decisions = ref false
let no_decisions_on = ref Util.SS.empty
let no_sat_learning = ref false
let sat_plugin = ref ""
let sat_solver = ref Util.CDCL_Tableaux

let set_arith_matching b = arith_matching := b
let set_bottom_classes b = bottom_classes := b
let set_cdcl_tableaux_inst b = cdcl_tableaux_inst := b
let set_cdcl_tableaux_th b = cdcl_tableaux_th := b
let set_disable_flat_formulas_simplification b =
  disable_flat_formulas_simplification := b
let set_enable_restarts b = enable_restarts := b
let set_minimal_bj b = minimal_bj := b
let set_no_backjumping b = no_backjumping := b
let set_no_backward b = no_backward := b
let set_no_decisions b = no_decisions := b
let set_no_decisions_on s = no_decisions_on := s
let set_no_sat_learning b = no_sat_learning := b
let set_sat_plugin p = sat_plugin := p
let set_sat_solver s = sat_solver := s

let get_arith_matching () = !arith_matching
let get_bottom_classes () = !bottom_classes
let get_cdcl_tableaux () = !cdcl_tableaux_th || !cdcl_tableaux_inst
let get_cdcl_tableaux_inst () = !cdcl_tableaux_inst
let get_cdcl_tableaux_th () = !cdcl_tableaux_th
let get_disable_flat_formulas_simplification () =
  !disable_flat_formulas_simplification
let get_enable_restarts () = !enable_restarts
let get_minimal_bj () = !minimal_bj
let get_no_backjumping () = !no_backjumping
let get_no_backward () = !no_backward
let get_no_decisions () = !no_decisions
let get_can_decide_on s =
  let ss = !no_decisions_on in
  ss == Util.SS.empty || not (Util.SS.mem s ss)
(* let get_no_decisions_on () = !no_decisions_on *)
let get_no_decisions_on_is_empty () = !no_decisions_on == Util.SS.empty
let get_no_sat_learning () = !no_sat_learning
let get_sat_learning () = not (!no_sat_learning)
let get_sat_plugin () = !sat_plugin
let get_sat_solver () = !sat_solver
let get_tableaux_cdcl () =
  match !sat_solver with
  | Tableaux_CDCL -> true
  | _ -> false

(** Term options *)

let disable_ites = ref false
let inline_lets = ref false
let rewriting = ref false
let term_like_pp = ref true

let set_disable_ites b = disable_ites := b
let set_inline_lets b = inline_lets := b
let set_rewriting b = rewriting := b
let set_term_like_pp b = term_like_pp := b

let get_disable_ites () = !disable_ites
let get_inline_lets () = !inline_lets
let get_rewriting () = !rewriting
let get_term_like_pp () = !term_like_pp

(** Theory options *)

let disable_adts = ref false
let no_ac = ref false
let no_contracongru = ref false
let no_fm = ref false
let no_nla = ref false
let no_tcp = ref false
let no_theory = ref false
let restricted = ref false
let tighten_vars = ref false

let set_disable_adts b = disable_adts := b
let set_no_ac b = no_ac := b
let set_no_contracongru b = no_contracongru := b
let set_no_fm b = no_fm := b
let set_no_nla b = no_nla := b
let set_no_tcp b = no_tcp := b
let set_no_theory b = no_theory := b
let set_restricted b = restricted := b
let set_tighten_vars b = tighten_vars := b

let get_disable_adts () = !disable_adts
let get_no_ac () = !no_ac
let get_no_contracongru () = !no_contracongru
let get_no_fm () = !no_fm
let get_no_nla () = !no_nla
let get_no_tcp () = !no_tcp
let get_no_theory () = !no_theory
let get_restricted () = !restricted
let get_tighten_vars () = !tighten_vars

(** Other options *)

let timers = ref false
let file = ref ""
let status = ref Status_Unknown
let session_file = ref ""
let used_context_file = ref ""

let set_timers b = timers := b
let set_status s = status := match_known_status s
let set_file f = file := f
let set_session_file f = session_file := f
let set_used_context_file f = used_context_file := f

let get_timers () = !timers || !profiling
let get_file () = !file
let get_status () = !status
let get_session_file () = !session_file
let get_used_context_file () = !used_context_file

(** particular getters : functions that are immediately executed **************)

let thread_yield = ref (fun () -> ())

let set_thread_yield f = thread_yield := f

let (timeout : (unit -> unit) ref) =
  ref (fun () -> raise Util.Timeout)

let set_timeout f = timeout := f

let exec_thread_yield () = !thread_yield ()
let exec_timeout () = !timeout ()

let tool_req n msg =
  if get_rule () = n then
    Format.fprintf (Output.get_fmt_diagnostic ()) "[rule] %s@." msg

(** Simple Timer module **)
module Time = struct

  let u = ref 0.0

  let current () = (Unix.times ()).tms_utime

  let start () = u := current ()

  let value () = current () -. !u

  let set_timeout timelimit =
    if Stdlib.(<>) timelimit 0. then
      let _ : Unix.interval_timer_status =
        Unix.setitimer Unix.ITIMER_VIRTUAL
          Unix.{ it_value = timelimit; it_interval = 0. }
      in
      ()

  let unset_timeout () =
    if Float.compare (get_timelimit ()) 0. <> 0 then
      let _ : Unix.interval_timer_status =
        Unix.setitimer Unix.ITIMER_VIRTUAL
          Unix.{ it_value = 0.; it_interval = 0. }
      in
      ()

  let with_timeout tm f =
    Fun.protect
      ~finally:unset_timeout
      (fun () ->
         set_timeout tm;
         f())
end

let with_timelimit_if cond f =
  if cond then
    Time.with_timeout (get_timelimit ()) f
  else
    f ()

(** globals **)

(* Printer **)
let pp_comment fmt msg =
  match get_output_format () with
  | Smtlib2 _ -> Format.fprintf fmt "; %s" msg;
  | Native | Why3 | Unknown _ -> Format.fprintf fmt "%s" msg

let[@inline always] heavy_assert p =
  assert (not @@ get_enable_assertions () || p ())
