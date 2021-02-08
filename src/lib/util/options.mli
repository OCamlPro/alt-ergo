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
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

(** {1 Options module used at start-up to parse the command line} *)

(** Some values are defined once and for all in the options module since it will
    be opened in each module. Even though it's not a good habit to do so this
    will stay like this until the next PR that's supposed to clean some parts
    of the program
*)

(** Type used to describe the type of models wanted *)
type model = MNone | MDefault | MAll | MComplete

(** Type used to describe the type of heuristic for instantiation wanted *)
type instantiation_heuristic  = INormal | IAuto | IGreedy

(** Type used to describe the type of input wanted by
    {!val:set_input_format} *)
type input_format =
  | Native                     (** Native Alt-Ergo format  *)
  | Smtlib2
  (** {{:
      http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf}
      Smtlib} default format *)
  | Why3                       (** Why3 file format *)
  (*   | SZS                        * Not yet implemented SZS format   *)
  | Unknown of string          (** Unknown file format *)

(** Type used to describe the type of output wanted by
    {!val:set_output_format} *)
type output_format = input_format

(** Type used to register the status, if known, of the input problem *)
type known_status =
    Status_Sat | Status_Unsat | Status_Unknown | Status_Undefined of string

(** {2 Setter functions} *)

(** {3 Setters for debug flags} *)

(** Set [debug] accessible with {!val:get_debug} *)
val set_debug : bool -> unit

(**Set [debug_ac] accessible with {!val:get_debug_ac} *)
val set_debug_ac : bool -> unit

(** Set [debug_adt] accessible with {!val:get_debug_adt} *)
val set_debug_adt : bool -> unit

(** Set [debug_arith] accessible with {!val:get_debug_arith} *)
val set_debug_arith : bool -> unit

(** Set [debug_arrays] accessible with {!val:get_debug_arrays} *)
val set_debug_arrays : bool -> unit

(** Set [debug_bitv] accessible with {!val:get_debug_bitv} *)
val set_debug_bitv : bool -> unit

(** Set [debug_cc] accessible with {!val:get_debug_cc} *)
val set_debug_cc : bool -> unit

(** Set [debug_combine] accessible with {!val:get_debug_combine} *)
val set_debug_combine : bool -> unit

(** Set [debug_constr] accessible with {!val:get_debug_constr} *)
val set_debug_constr : bool -> unit

(** Set [debug_explanations] accessible with {!val:get_debug_explanations} *)
val set_debug_explanations : bool -> unit

(** Set [debug_fm] accessible with {!val:get_debug_fm} *)
val set_debug_fm : bool -> unit

(** Set [debug_fpa] accessible with {!val:get_debug_fpa} *)
val set_debug_fpa : int -> unit

(** Set [debug_gc] accessible with {!val:get_debug_gc} *)
val set_debug_gc : bool -> unit

(** Set [debug_interpretation] accessible with
    {!val:get_debug_interpretation} *)
val set_debug_interpretation : bool -> unit

(** Set [debug_ite] accessible with {!val:get_debug_ite} *)
val set_debug_ite : bool -> unit

(** Set [debug_matching] accessible with {!val:get_debug_matching}

    Possible values are
    {ol {- Disabled} {- Light} {- Full}}
*)
val set_debug_matching : int -> unit

(** Set [debug_sat] accessible with {!val:get_debug_sat} *)
val set_debug_sat : bool -> unit

(** Set [debug_split] accessible with {!val:get_debug_split} *)
val set_debug_split : bool -> unit

(** Set [debug_sum] accessible with {!val:get_debug_sum} *)
val set_debug_sum : bool -> unit

(** Set [debug_triggers] accessible with {!val:get_debug_triggers} *)
val set_debug_triggers : bool -> unit

(** Set [debug_types] accessible with {!val:get_debug_types} *)
val set_debug_types : bool -> unit

(** Set [debug_typing] accessible with {!val:get_debug_typing} *)
val set_debug_typing : bool -> unit

(** Set [debug_uf] accessible with {!val:get_debug_uf} *)
val set_debug_uf : bool -> unit

(** Set [debug_unsat_core] accessible with {!val:get_debug_unsat_core} *)
val set_debug_unsat_core : bool -> unit

(** Set [debug_use] accessible with {!val:get_debug_use} *)
val set_debug_use : bool -> unit

(** Set [debug_warnings] accessible with {!val:get_debug_warnings} *)
val set_debug_warnings : bool -> unit

(** Set [profiling] accessible with {!val:get_profiling} *)
val set_profiling : bool -> float -> unit

(** Set [timers] accessible with {!val:get_timers} *)
val set_timers : bool -> unit

(** {3 Additional setters} *)

(** Set [type_only] accessible with {!val:get_type_only} *)
val set_type_only : bool -> unit

(** Set [age_bound] accessible with {!val:get_age_bound} *)
val set_age_bound : int -> unit

(** Set [bottom_classes] accessible with {!val:get_bottom_classes} *)
val set_bottom_classes : bool -> unit

(** Set [fm_cross_limit] accessible with {!val:get_fm_cross_limit} *)
val set_fm_cross_limit : Numbers.Q.t -> unit

(** Set [frontend] accessible with {!val:get_frontend} *)
val set_frontend : string -> unit

(** Set [instantiation_heuristic ] accessible with
    {!val:get_instantiation_heuristic} *)
val set_instantiation_heuristic : instantiation_heuristic -> unit

(** Set [inline_lets] accessible with {!val:get_inline_lets} *)
val set_inline_lets : bool -> unit

(** Set [input_format] accessible with {!val:get_input_format} *)
val set_input_format : input_format -> unit

(** Set [interpretation] accessible with {!val:get_interpretation}

    Possible values are :
    {ol {- Unknown} {- Before instantiation}
    {- Before every decision or instantiation}}

    A negative value (-1, -2, or -3) will disable interpretation display. *)
val set_interpretation : int -> unit

(** Set [max_split] accessible with {!val:get_max_split} *)
val set_max_split : Numbers.Q.t -> unit

(** Set [model] accessible with {!val:get_model}

    Possible values are :
    {ul {- Default} {- Complete} {- All}}
*)
val set_model : model -> unit

(** Set [nb_triggers] accessible with {!val:get_nb_triggers} *)
val set_nb_triggers : int -> unit

(** Set [no_ac] accessible with {!val:get_no_ac} *)
val set_no_ac : bool -> unit

(** Set [no_contragru] accessible with {!val:get_no_contragru} *)
val set_no_contracongru : bool -> unit

(** Set [no_ematching] accessible with {!val:get_no_ematching} *)
val set_no_ematching : bool -> unit

(** Set [no_nla] accessible with {!val:get_no_nla} *)
val set_no_nla : bool -> unit

(** Set [no_user_triggers] accessible with {!val:get_no_user_triggers} *)
val set_no_user_triggers : bool -> unit

(** Set [normalize_instances] accessible with {!val:get_normalize_instances} *)
val set_normalize_instances : bool -> unit

(** Set [output_format] accessible with {!val:get_output_format} *)
val set_output_format : output_format -> unit

(** Set [parse_only] accessible with {!val:get_parse_only} *)
val set_parse_only : bool -> unit

(** Set [restricted] accessible with {!val:get_restricted} *)
val set_restricted : bool -> unit

(** Set [rewriting] accessible with {!val:get_rewriting} *)
val set_rewriting : bool -> unit

(** Set [rule] accessible with {!val:get_rule} *)
val set_rule : int -> unit

(** Set [save_used_context] accessible with {!val:get_save_used_context} *)
val set_save_used_context : bool -> unit

(** Set [steps_bound] accessible with {!val:get_steps_bound} *)
val set_steps_bound : int -> unit

(** Set [term_like_pp] accessible with {!val:get_term_like_pp} *)
val set_term_like_pp : bool -> unit

(** Set [thread_yield] accessible with {!val:get_thread_yield} *)
val set_thread_yield : (unit -> unit) -> unit

(** Set [timelimit] accessible with {!val:get_timelimit} *)
val set_timelimit : float -> unit

(** Set [timeout] accessible with {!val:get_timeout} *)
val set_timeout : (unit -> unit) -> unit

(** Set [triggers_var] accessible with {!val:get_triggers_var} *)
val set_triggers_var : bool -> unit

(** Set [type_smt2] accessible with {!val:get_type_smt2} *)
val set_type_smt2 : bool -> unit

(** Set [unsat_core] accessible with {!val:get_unsat_core} *)
val set_unsat_core : bool -> unit

(** Set [verbose] accessible with {!val:get_verbose} *)
val set_verbose : bool -> unit

(** Set [status] accessible with {!val:get_status} *)
val set_status : string -> unit

(** Set [file] accessible with {!val:get_file} *)
val set_file : string -> unit

(** Updates the filename to be parsed and sets a js_mode flag *)
val set_file_for_js : string -> unit

(** Setters used by parse_command *)

(** Set [case_split_policy] accessible with {!val:get_case_split_policy}  *)
val set_case_split_policy : Util.case_split_policy -> unit

(** Set [enable_adts_cs] accessible with {!val:get_enable_adts_cs} *)
val set_enable_adts_cs : bool -> unit

(** Set [replay] accessible with {!val:get_replay} *)
val set_replay : bool -> unit

(** Set [replay_all_used_context] accessible with
    {!val:get_replay_all_used_context} *)
val set_replay_all_used_context : bool -> unit

(** Set [replay_used_context] accessible with {!val:get_replay_used_context} *)
val set_replay_used_context : bool -> unit

(** Set [answers_with_loc] accessible with {!val:get_answers_with_loc} *)
val set_answers_with_loc : bool -> unit

(** Set [output_with_colors] accessible with {!val:get_output_with_colors} *)
val set_output_with_colors : bool -> unit

(** Set [output_with_headers] accessible with {!val:get_output_with_headers} *)
val set_output_with_headers : bool -> unit

(** Set [output_with_formatting] accessible with
    {!val:get_output_with_formatting} *)
val set_output_with_formatting : bool -> unit

(** Set [output_with_forced_flush] accessible with
    {!val:get_output_with_forced_flush} *)
val set_output_with_forced_flush : bool -> unit

(** Set [infer_input_format] accessible with {!val:get_infer_input_format} *)
val set_infer_input_format : 'a option -> unit

(** Set [infer_output_format] accessible with {!val:get_infer_output_format} *)
val set_infer_output_format : 'a option -> unit

(** Set [parsers] accessible with {!val:get_parsers} *)
val set_parsers : string list -> unit

(** Set [preludes] accessible with {!val:get_preludes} *)
val set_preludes : string list -> unit

(** Set [disable_weaks] accessible with {!val:get_disable_weaks} *)
val set_disable_weaks : bool -> unit

(** Set [enable_assertions] accessible with {!val:get_enable_assertions} *)
val set_enable_assertions : bool -> unit

(** Set [warning_as_error] accessible with {!val:get_warning_as_error} *)
val set_warning_as_error : bool -> unit

(** Set [timelimit_interpretation] accessible with
    {!val:get_timelimit_interpretation} *)
val set_timelimit_interpretation : float -> unit

(** Set [timelimit_per_goal] accessible with {!val:get_timelimit_per_goal} *)
val set_timelimit_per_goal : bool -> unit

(** Set [cumulative_time_profiling] accessible with
    {!val:get_cumulative_time_profiling} *)
val set_cumulative_time_profiling : bool -> unit

(** Set [profiling_period] accessible with {!val:get_profiling_period} *)
val set_profiling_period : float -> unit

(** Set [profiling_plugin] accessible with {!val:get_profiling_plugin} *)
val set_profiling_plugin : string -> unit

(** Set [instantiate_after_backjump] accessible with
    {!val:get_instantiate_after_backjump} *)
val set_instantiate_after_backjump : bool -> unit

(** Set [max_multi_triggers_size] accessible with
    {!val:get_max_multi_triggers_size} *)
val set_max_multi_triggers_size : int -> unit

(** Set [arith_matching] accessible with {!val:get_arith_matching} *)
val set_arith_matching : bool -> unit

(** Set [cdcl_tableaux_inst] accessible with {!val:get_cdcl_tableaux_inst} *)
val set_cdcl_tableaux_inst : bool -> unit

(** Set [cdcl_tableaux_th] accessible with {!val:get_cdcl_tableaux_th} *)
val set_cdcl_tableaux_th : bool -> unit

(** Set [disable_flat_formulas_simplification] accessible
    with {!val:get_disable_flat_formulas_simplification} *)
val set_disable_flat_formulas_simplification : bool -> unit

(** Set [enable_restarts] accessible with {!val:get_enable_restarts} *)
val set_enable_restarts : bool -> unit

(** Set [minimal_bj] accessible with {!val:get_minimal_bj} *)
val set_minimal_bj : bool -> unit

(** Set [no_backjumping] accessible with {!val:get_no_backjumping} *)
val set_no_backjumping : bool -> unit

(** Set [no_backward] accessible with {!val:get_no_backward} *)
val set_no_backward : bool -> unit

(** Set [no_decisions] accessible with {!val:get_no_decisions} *)
val set_no_decisions : bool -> unit

(** Set [no_decisions_on] accessible with {!val:get_no_decisions_on} *)
val set_no_decisions_on : Util.SS.t -> unit

(** Set [no_sat_learning] accessible with {!val:get_no_sat_learning} *)
val set_no_sat_learning : bool -> unit

(** Set [sat_plugin] accessible with {!val:get_sat_plugin} *)
val set_sat_plugin : string -> unit

(** Set [sat_solver] accessible with {!val:get_sat_solver} *)
val set_sat_solver : Util.sat_solver -> unit

(** Set [tableaux_cdcl] accessible with {!val:get_tableaux_cdcl} *)
val set_tableaux_cdcl : bool -> unit

(** Set [disable_ites] accessible with {!val:get_disable_ites} *)
val set_disable_ites : bool -> unit

(** Set [disable_adts] accessible with {!val:get_disable_adts} *)
val set_disable_adts : bool -> unit

(** Set [inequalities_plugin] accessible with {!val:get_inequalities_plugin} *)
val set_inequalities_plugin : string -> unit

(** Set [no_fm] accessible with {!val:get_no_fm} *)
val set_no_fm : bool -> unit

(** Set [no_tcp] accessible with {!val:get_no_tcp} *)
val set_no_tcp : bool -> unit

(** Set [no_theory] accessible with {!val:get_no_theory} *)
val set_no_theory : bool -> unit

(** Set [tighten_vars] accessible with {!val:get_tighten_vars} *)
val set_tighten_vars : bool -> unit

(** Set [use_fpa] accessible with {!val:get_use_fpa} *)
val set_use_fpa : bool -> unit

(** Set [session_file] accessible with {!val:get_session_file} *)
val set_session_file : string -> unit

(** Set [used_context_file] accessible with {!val:get_used_context_file} *)
val set_used_context_file : string -> unit

(** {2 Getter functions} *)

(** {3 Getters for debug flags} *)
(** Default value for all the debug flags is [false] *)

(** Get the debugging flag. *)
val get_debug : unit -> bool

(** Get the debugging flag of warnings. *)
val get_debug_warnings : unit -> bool

(** Get the debugging flag of cc. *)
val get_debug_cc : unit -> bool

(** Prints some debug info about the GC's activity. *)
val get_debug_gc : unit -> bool

(** Get the debugging flag of use. *)
val get_debug_use : unit -> bool

(** Get the debugging flag of uf. *)
val get_debug_uf : unit -> bool

(** Get the debugging flag of inequalities. *)
val get_debug_fm : unit -> bool

(** Get the debugging value of floating-point. *)
val get_debug_fpa : unit -> int
(** Default to [0]. *)

(** Get the debugging flag of Sum. *)
val get_debug_sum : unit -> bool

(** Get the debugging flag of ADTs. *)
val get_debug_adt : unit -> bool

(** Get the debugging flag of Arith (without fm). *)
val get_debug_arith : unit -> bool

(** Get the debugging flag of bitv. *)
val get_debug_bitv : unit -> bool

(** Get the debugging flag of ac. *)
val get_debug_ac : unit -> bool

(** Get the debugging flag of SAT. *)
val get_debug_sat : unit -> bool

(** Get the debugging flag of typing. *)
val get_debug_typing : unit -> bool

(** Get the debugging flag of constructors. *)
val get_debug_constr : unit -> bool

(** Get the debugging flag of arrays. *)
val get_debug_arrays : unit -> bool

(** Get the debugging flag of ite. *)
val get_debug_ite : unit -> bool

(** Get the debugging flag of types. *)
val get_debug_types : unit -> bool

(** Get the debugging flag of combine. *)
val get_debug_combine : unit -> bool

(** Replay unsat-cores produced by {!val:get_unsat_core}.
    The option implies {!val:get_unsat_core} returns [true]. *)
val get_debug_unsat_core : unit -> bool

(** Get the debugging flag of case-split analysis. *)
val get_debug_split : unit -> bool

(** Get the debugging flag of E-matching

    Possible values are
    {ol {- Disabled} {- Light} {- Full}}
*)
val get_debug_matching : unit -> int

(** Get the debugging flag of explanations. *)
val get_debug_explanations : unit -> bool

(** Get the debugging flag of triggers. *)
val get_debug_triggers : unit -> bool

(** Get the debugging flag for interpretation generatation. *)
val get_debug_interpretation : unit -> bool

(** {3 Additional getters} *)

(** {4 Case-split options} *)

(** Value specifying the case-split policy.

    Possible values are :
    {ul {- after-theory-assume} {- before-matching} {- after-matching}}

*)
val get_case_split_policy : unit -> Util.case_split_policy
(** Default to [after-theory-assume] *)

(** [true] if case-split for Algebraic Datatypes theory is enabled. *)
val get_enable_adts_cs : unit -> bool
(** Default to [false] *)

(** Valuget_e specifying the maximum size of case-split. *)
val get_max_split : unit -> Numbers.Q.t
(** Default to [1_000_000] *)

(** {4 Context options} *)

(** [true] if replay session will be saved in [file_name.agr]. *)
val get_replay : unit -> bool
(** Default to [false] *)

(** [true] if replay with all axioms and predicates saved in [.used] files
    of the current directory is enabled. *)
val get_replay_all_used_context : unit -> bool
(** Default to [false] *)

(** [true] if replay with axioms and predicates saved in [.used] file
    is enabled. *)
val get_replay_used_context : unit -> bool
(** Default to [false] *)

(** [true] if used axioms and predicates will be saved in a [.used] file.
    This option implies {!val:get_unsat_core} returns [true]. *)
val get_save_used_context : unit -> bool
(** Default to [false] *)

(** {4 Execution options} *)

(** [true] if the locations of goals is shown when printing solver's answers. *)
val get_answers_with_locs  : unit -> bool
(** Default to [true] *)

(** [true] if the outputs are printed with colors *)
val get_output_with_colors  : unit -> bool
(** Default to [true] *)

(** [true] if the outputs are printed with headers *)
val get_output_with_headers  : unit -> bool
(** Default to [true] *)

(** [true] if the outputs are printed with formatting rules *)
val get_output_with_formatting  : unit -> bool
(** Default to [true] *)

(** [true] if the outputs are flushed at the end of every print *)
val get_output_with_forced_flush  : unit -> bool
(** Default to [true] *)

(** Valuget_e of the currently selected parsing and typing frontend. *)
val get_frontend : unit -> string
(** Default to [legacy] *)

(** Value specifying the default input format. Useful when the extension
    does not allow to automatically select a parser (eg. JS mode, GUI
    mode, ...). possible values are
    {ul {- native} {- smtlib2} {- why3}} *)
val get_input_format : unit -> input_format
(** Default to [Native] *)

(** [true] if Alt-Ergo infers automatically the input format according to the
    file extension. [false] if an input format is set with -i option *)
val get_infer_input_format : unit -> bool
(** Default to [true] *)

(** [true] if the program shall stop after parsing. *)
val get_parse_only : unit -> bool
(** Default to [false] *)

(** List of registered parsers for Alt-Ergo. *)
val get_parsers : unit -> string list
(** Default to [false] *)

(** List of files that have be loaded as preludes. *)
val get_preludes : unit -> string list
(** Default to [\[\]] *)

(** [true] if the program shall stop after typing. *)
val get_type_only : unit -> bool
(** Default to [false] *)

(** [true] if the program shall stop after SMT2 typing. *)
val get_type_smt2 : unit -> bool
(** Default to [false] *)

(** {4 Internal options} *)

(** [true] if the GC is prevented from collecting hashconsed data structrures
    that are not reachable (useful for more determinism). *)
val get_disable_weaks : unit -> bool
(** Default to [false] *)

(** [true] if verification of some heavy invariants is enabled. *)
val get_enable_assertions : unit -> bool
(** Default to [false] *)

(** [true] if warning are set as error. *)
val get_warning_as_error : unit -> bool
(** Default to [false] *)

(** {4 Limit options} *)

(** Value specifying the age limit bound. *)
val get_age_bound : unit -> int
(** Default to [50] *)

(** Value specifying the limit above which Fourier-Motzkin variables elimination
    steps that may produce a number of inequalities that is greater than this
    limit are skipped.
    However, unit eliminations are always done. *)
val get_fm_cross_limit : unit -> Numbers.Q.t
(** Default to [10_000] *)

(** Value specifying the maximum number of steps. *)
val get_steps_bound : unit -> int
(** Default to [-1] *)

(** Value specifying the time limit (not supported on Windows). *)
val get_timelimit : unit -> float
(** Default to [0.] *)

(** Value specifying the time limit for model generation
    (not supported on Windows). *)
val get_timelimit_interpretation : unit -> float
(** Default to [1.] (not supported on Windows) *)

(** Value specifying the given timelimit for each goal in case of multiple
    goals per file. In this case, time spent in preprocessing is separated from
    resolution time.

    ${i Not relevant for GUI-mode.} *)
val get_timelimit_per_goal : unit -> bool
(** Default to [false] *)

(** {4 Output options} *)

(** Experimental support for models on labeled terms.

    Possible values are
    {ul {- None} {- Default} {- Complete : shows a complete model}
    {- All : shows all models}}

    Which are used in the two setters below. This option answers
    [true] if the model is set to Default or Complete
*)
val get_model : unit -> bool
(** Default to [false] *)

(** [true] if the model is set to complete model *)
val get_complete_model : unit -> bool
(** Default to [false] *)

(** [true] if the model is set to all models? *)
val get_all_models : unit -> bool
(** Default to [false] *)

(** Experimental support for counter-example generation.

    Possible values are :
    {ol {- Unknown} {- Before instantiation}
    {- Before every decision or instantiation}}

    A negative value (-1, -2, or -3) will disable interpretation display.

    Note that {!val:get_max_split} limitation will be ignored in model
    generation phase. *)
val get_interpretation : unit -> int
(** Default to [0] *)

(** Value specifying the default output format. possible values are
    {ul {- native} {- smtlib2} {- why3}}
    . *)
val get_output_format : unit -> output_format
(** Default to [Native] *)

(** [true] if Alt-Ergo infers automatically the output format according to the
    the file extension or the input format if set. *)
val get_infer_output_format : unit -> bool
(** Default to [true] *)

(** [true] if experimental support for unsat-cores is on. *)
val get_unsat_core : unit -> bool
(** Default to [false] *)

(** {4 Profiling options} *)

(** [true] if the profiling module is activated.

    Use Ctrl-C to switch between different views and Ctrl + AltGr + \ to exit.
*)
val get_profiling : unit -> bool
(** Default to [false] *)

(** Value specifying the profiling module frequency.*)
val get_profiling_period : unit -> float
(** Default to [0.] *)

(** [true] if the time spent in called functions is recorded in callers *)
val get_cumulative_time_profiling : unit -> bool
(** Default to [false] *)

(** Value specifying which module is used as a profiling plugin. *)
val get_profiling_plugin : unit -> string
(** Default to [false] *)

(** [true] if profiling is set to true (automatically enabled) *)
val get_timers : unit -> bool
(** Default to [false] *)

(** [true] if the verbose mode is activated. *)
val get_verbose : unit -> bool
(** Default to [false] *)

(** {4 Quantifier options} *)

(** Value specifying the instantiation heuristic. possible values are
    {ul {- normal} {- auto} {- greedy}}. *)
val get_instantiation_heuristic : unit -> instantiation_heuristic
(** Default to [IAuto] *)

(** [true] is the greedy instantiation heuristic is set *)
val get_greedy : unit -> bool
(** Default to [false] *)

(** [true] if a (normal) instantiation round is made after every
    backjump/backtrack.*)
val get_instantiate_after_backjump : unit -> bool
(** Default to [false] *)

(** Value specifying the max number of terms allowed in multi-triggers. *)
val get_max_multi_triggers_size : unit -> int
(** Default to [4] *)

(** [true] if variables are allowed as triggers. *)
val get_triggers_var : unit -> bool
(** Default to [false] *)

(** Value specifying the number of (multi)triggers. *)
val get_nb_triggers : unit -> int
(** Default to [2] *)

(** [true] if matching modulo ground equalities is disabled. *)
val get_no_ematching : unit -> bool
(** Default to [false] *)

(** [true] if user triggers are ignored except for triggers
    of theories axioms *)
val get_no_user_triggers : unit -> bool
(** Default to [false] *)

(** [true] if generated substitutions are normalised by matching w.r.t.
    the state of the theory.

    This means that only terms that are greater (w.r.t. depth)
    than the initial terms of the problem are normalized. *)
val get_normalize_instances : unit -> bool
(** Default to [false] *)

(** {4 SAT options} *)

(** [true] if (the weak form of) matching modulo linear arithmetic
    is disabled. *)
val get_arith_matching : unit -> bool
(** Default to [true] *)

(** [true] if backjumping mechanism in the functional SAT solver is disabled. *)
val get_no_backjumping : unit -> bool
(** Default to [false] *)

(** [true] if equivalence classes at each bottom of the SAT are shown. *)
val get_bottom_classes : unit -> bool
(** Default to [false] *)

(** Value specifying which SAT solver is being used.

    Possible values are:
    {ul {- CDCL-tableaux : CDCL SAT-solver with
    formulas filtering based on tableaux method
    {ul {- satML-Tableaux} {- satML-tableaux}}}
    {- CDCL : CDCL SAT-solver
    {ul {- satML}}}
    {- Tableaux : SAT-solver based on tableaux method
    {ul {- tableaux} {- tableaux-like} {- Tableaux-like}}}
    {- Tableaux-CDCL : Tableaux method assisted with a CDCL SAT-solver
    {ul {- tableaux-cdcl} {- tableaux-CDCL} {- Tableaux-cdcl}}}
    }
*)
val get_sat_solver : unit -> Util.sat_solver
(** Default to [CDCL-tableaux] *)

(** [true] if the use of a tableaux-like method for instantiations
    is enabled with the CDCL solver if satML is used. *)
val get_cdcl_tableaux_inst : unit -> bool
(** Default to [true] *)

(** [true] if the use of a tableaux-like method for theories
    is enabled with the CDCL solver if satML is used. *)
val get_cdcl_tableaux_th : unit -> bool
(** Default to [true] *)

(** [true] if the use of a tableaux-like method for theories or instantiations
    is enabled with the CDCL solver if satML is used. *)
val get_cdcl_tableaux : unit -> bool
(** Default to [true] *)

(** [true] if the tableaux SAT-solver is used with CDCL assist. *)
val get_tableaux_cdcl : unit -> bool
(** Default to [false] *)

(** [true] if minimal backjumping in satML CDCL solver is enabled *)
val get_minimal_bj : unit -> bool
(** Default to [true] *)

(** [true] if restarts are enabled for satML. *)
val get_enable_restarts : unit -> bool
(** Default to [false] *)

(** [true] if facts simplification is disabled in satML's flat formulas. *)
val get_disable_flat_formulas_simplification : unit -> bool
(** Default to [false] *)


val get_no_sat_learning : unit -> bool
val get_sat_learning : unit -> bool
(** [true] if learning/caching of unit facts in the Default SAT is disabled.
    These facts are used to improve bcp.

    Default to [true] (sat_learning is active) *)

(** Value specifying which SAT-solver is used. *)
val get_sat_plugin : unit -> string
(** Default to [false] *)

(** {4 Term options} *)

(** [true] if handling of ite(s) on terms in the backend is disabled. *)
val get_disable_ites : unit -> bool
(** Default to [false] *)

(** [true] if substitution of variables bounds by Let is enabled. The default
    behavior is to only substitute variables that are bound to a
    constant, or that appear at most once. *)
val get_inline_lets : unit -> bool
(** Default to [false] *)

(** [true] if rewriting is used instead of axiomatic approach. *)
val get_rewriting : unit -> bool
(** Default to [false] *)

(** [true] if semantic values shall be output as terms. *)
val get_term_like_pp : unit -> bool
(** Default to [true] *)

(** {4 Theory options} *)

(** [true] if Algebraic Datatypes theory is disabled *)
val get_disable_adts : unit -> bool
(** Default to [false] *)

(** Value specifying which module is used to handle inequalities
    of linear arithmetic. *)
val get_inequalities_plugin : unit -> string
(** Default to [false] *)

(** [true] if the AC (Associative and Commutative) theory is disabled
    for function symbols. *)
val get_no_ac : unit -> bool
(** Default to [false] *)

(** [true] if contracongru is disabled. *)
val get_no_contracongru : unit -> bool
(** Default to [false] *)

(** [true] if Fourier-Motzkin algorithm is disabled. *)
val get_no_fm : unit -> bool
(** Default to [false] *)

(** [true] if non-linear arithmetic reasoning (i.e. non-linear
    multplication, division and modulo on integers and rationals) is disabled.
    Non-linear multiplication remains AC. *)
val get_no_nla : unit -> bool
(** Default to [false] *)

(** [true] if BCP modulo theories is deactivated. *)
val get_no_tcp : unit -> bool
(** Default to [false] *)

(** [true] if backward reasoning step (starting from the goal) done in
    the default SAT solver before deciding is disabled. *)
val get_no_backward : unit -> bool
(** Default to [false] *)

(** [true] if decisions at the SAT level are disabled. *)
val get_no_decisions : unit -> bool
(** Default to [false] *)

(** [true] if theory reasoning is completely deactivated. *)
val get_no_theory : unit -> bool
(** Default to [false] *)

(** [true] if the set of decision procedures (equality, arithmetic and AC)
    is restricted. *)
val get_restricted : unit -> bool
(** Default to [false] *)

(** [true] if the best bounds for arithmetic variables is computed. *)
val get_tighten_vars : unit -> bool
(** Default to [false] *)

(** [true] if support for floating-point arithmetic is enabled. *)
val get_use_fpa : unit -> bool
(** Default to [false] *)

(** Possible values are
    {ul {- 0 : parsing} {- 1 : typing} {- 2 : sat} {- 3 : cc} {- 4 : arith}}

    output rule used on stderr. *)
val get_rule : unit -> int
(** Default to [-1] *)

(** {4 Files} *)

(** Value specifying the status of the file given to Alt-Ergo *)
val get_status : unit -> known_status
(** Default to [Status_Unknown] *)

(** [true] if the JavaScript mode is activated *)
val get_js_mode : unit -> bool
(** Default to [false] *)

(** Value specifying the file given to Alt-Ergo *)
val get_file : unit -> string
(** Default to [""] *)

(** Value specifying the session file ([base_name.agr]) handled by Alt-Ergo *)
val get_session_file : unit -> string
(** Default to [false] *)

(** Value specifying the base name of the file (with no extension) *)
val get_used_context_file : unit -> string
(** Default to [false] *)



(** {2 Functions that are immediately executed} *)

val exec_thread_yield : unit -> unit
val exec_timeout : unit -> unit

(** {2 Simple Timer module} *)

module Time : sig


  val start : unit -> unit
  val value : unit -> float

  val set_timeout : is_gui:bool -> float -> unit
  val unset_timeout : is_gui:bool -> unit

end

(** {2 Globals} *)
(** Global functions used throughout the whole program *)

(** Displays the used rule *)
val tool_req : int -> string -> unit

(** {3 Monomorphisations}  *)
(** Since {!module:Options} is opened in every module,
    definition of binary operators to hide their polymorphic
    versions {{:https://caml.inria.fr/pub/docs/manual-ocaml/libref/Stdlib.html}
    [Stdlib]} *)

val (<>) : int -> int -> bool
val (=) : int -> int -> bool
val (<) : int -> int -> bool
val (>) : int -> int -> bool
val (<=) : int -> int -> bool
val (>=) : int -> int -> bool

val compare : int -> int -> int

val get_can_decide_on : string -> bool
val get_no_decisions_on_is_empty : unit -> bool

(** Extra *)
val match_extension : string -> input_format

val set_is_gui : bool -> unit
val get_is_gui : unit -> bool


(** {3 Printer and formatter } *)
(** This functions are use to print or set the formatter used to output results
    debug or error informations *)

(** Print message as comment in the corresponding output format *)
val print_output_format: Format.formatter -> string -> unit

(** Set the std formatter used by default to output the results [fmt_std],
    model [fmt_mdl] and unsat core [fmt_usc]. *)
val set_std_fmt : Format.formatter -> unit
(** Default to [Format.std_formatter] *)

(** Set the err formatter used by default to output error [fmt_err],
    debug [fmt_dbg] and warning [fmt_wrn] informations. *)
val set_err_fmt : Format.formatter -> unit
(** Default to [Format.err_formatter] *)

(** Value specifying the formatter used to output results *)
val get_fmt_std : unit -> Format.formatter
(** Default to [Format.std_formatter] *)

(** Value specifying the formatter used to output errors *)
val get_fmt_err : unit -> Format.formatter
(** Default to [Format.err_formatter] *)

(** Value specifying the formatter used to output warnings *)
val get_fmt_wrn : unit -> Format.formatter
(** Default to [Format.err_formatter] *)

(** Value specifying the formatter used to output debug informations *)
val get_fmt_dbg : unit -> Format.formatter
(** Default to [Format.err_formatter] *)

(** Value specifying the formatter used to output model *)
val get_fmt_mdl : unit -> Format.formatter
(** Default to [Format.std_formatter] *)

(** Value specifying the formatter used to output unsat core *)
val get_fmt_usc : unit -> Format.formatter
(** Default to [Format.std_formatter] *)

(** Set [fmt_std] accessible with {!val:get_fmt_std} *)
val set_fmt_std : Format.formatter -> unit

(** Set [fmt_err] accessible with {!val:get_fmt_err} *)
val set_fmt_err : Format.formatter -> unit

(** Set [fmt_wrn] accessible with {!val:get_fmt_wrn} *)
val set_fmt_wrn : Format.formatter -> unit

(** Set [fmt_dbg] accessible with {!val:get_fmt_dbg} *)
val set_fmt_dbg : Format.formatter -> unit

(** Set [fmt_mdl] accessible with {!val:get_fmt_mdl} *)
val set_fmt_mdl : Format.formatter -> unit

(** Set [fmt_usc] accessible with {!val:get_fmt_usc} *)
val set_fmt_usc : Format.formatter -> unit
