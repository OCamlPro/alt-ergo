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

(** Standard output formatter for
    {{:https://caml.inria.fr/pub/docs/manual-ocaml/libref/Format.html} Format}
*)
val fmt : Format.formatter

(** Type used to describe the type of models wanted *)
type model = MNone | MDefault | MAll | MComplete

(** Type used to describe the type of output wanted by {!val:set_output_format}
*)
type output =
  | ONative                     (** Native Alt-Ergo format  *)
  | OSmtlib
  (** {{:
      http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf}
      Smtlib} default format *)
  | OSZS                        (** Not yet implemented SZS format  *)

(** {2 Setter functions} *)

(** {3 Setters for debug flags} *)

(** Set {!val:debug} *)
val set_debug : bool -> unit

(**Set {!val:debug_ac} *)
val set_debug_ac : bool -> unit

(** Set {!val:debug_adt} *)
val set_debug_adt : bool -> unit

(** Set {!val:debug_arith} *)
val set_debug_arith : bool -> unit

(** Set {!val:debug_arrays} *)
val set_debug_arrays : bool -> unit

(** Set {!val:debug_bitv} *)
val set_debug_bitv : bool -> unit

(** Set {!val:debug_cc} *)
val set_debug_cc : bool -> unit

(** Set {!val:debug_combine} *)
val set_debug_combine : bool -> unit

(** Set {!val:debug_constr} *)
val set_debug_constr : bool -> unit

(** Set {!val:debug_explanations} *)
val set_debug_explanations : bool -> unit

(** Set {!val:debug_fm} *)
val set_debug_fm : bool -> unit

(** Set {!val:debug_gc} *)
val set_debug_gc : bool -> unit

(** Set {!val:debug_ite} *)
val set_debug_ite : bool -> unit

(** Set {!val:debug_matching}

    Possible values are
    {ol {- Disabled} {- Light} {- Full}}
*)
val set_debug_matching : int -> unit

(** Set {!val:debug_sat} *)
val set_debug_sat : bool -> unit

(** Set {!val:debug_sat_simple} *)
val set_debug_sat_simple : bool -> unit

(** Set {!val:debug_split} *)
val set_debug_split : bool -> unit

(** Set {!val:debug_sum} *)
val set_debug_sum : bool -> unit

(** Set {!val:debug_types} *)
val set_debug_types : bool -> unit

(** Set {!val:debug_typing} *)
val set_debug_typing : bool -> unit

(** Set {!val:debug_uf} *)
val set_debug_uf : bool -> unit

(** Set {!val:debug_unsat_core} *)
val set_debug_unsat_core : bool -> unit

(** Set {!val:debug_use} *)
val set_debug_use : bool -> unit

(** Set {!val:profiling} *)
val set_profiling : float -> bool -> unit

(** Set {!val:timers} *)
val set_timers : bool -> unit

(** {3 Additional setters} *)

(** Set {!val:type_only} *)
val set_type_only : bool -> unit

(** Set {!val:age_bound} *)
val set_age_bound : int -> unit

(** Set {!val:bottom_classes} *)
val set_bottom_classes : bool -> unit

(** Set {!val:fm_cross_limit} *)
val set_fm_cross_limit : Numbers.Q.t -> unit

(** Set {!val:frontend} *)
val set_frontend : string -> unit

(** Set {!val:greedy} *)
val set_greedy : bool -> unit

(** Set {!val:inline_lets} *)
val set_inline_lets : bool -> unit

(** Set {!val:input_format} *)
val set_input_format : string -> unit

(** Set {!val:interpretation}

    Possible values are :
    {ol {- Unknown} {- Before instantiation}
    {- Before every decision or instantiation}}

    A negative value (-1, -2, or -3) will disable interpretation display. *)
val set_interpretation : int -> unit

(** Set {!val:max_split} *)
val set_max_split : Numbers.Q.t -> unit

(** Set {!val:model}

    Possible values are :
    {ul {- Default} {- Complete} {- All}}
*)
val set_model : model -> unit

(** Set {!val:nb_triggers} *)
val set_nb_triggers : int -> unit

(** Set {!val:no_ac} *)
val set_no_ac : bool -> unit

(** Set {!val:no_contragru} *)
val set_no_contracongru : bool -> unit

(** Set {!val:no_ematching} *)
val set_no_ematching : bool -> unit

(** Set {!val:no_nla} *)
val set_no_nla : bool -> unit

(** Set {!val:no_user_triggers} *)
val set_no_user_triggers : bool -> unit

(** Set {!val:normalize_instances} *)
val set_normalize_instances : bool -> unit

(** Set {!val:output_format} *)
val set_output_format : output -> unit

(** Set {!val:parse_only} *)
val set_parse_only : bool -> unit

(** Set {!val:restricted} *)
val set_restricted : bool -> unit

(** Set {!val:rewriting} *)
val set_rewriting : bool -> unit

(** Set {!val:rules} *)
val set_rules : int -> unit

(** Set {!val:save_used_context} *)
val set_save_used_context : bool -> unit

(** Set {!val:steps_bound} *)
val set_steps_bound : int -> unit

(** Set {!val:term_like_pp} *)
val set_term_like_pp : bool -> unit

(** Set {!val:thread_yield} *)
val set_thread_yield : (unit -> unit) -> unit

(** Set {!val:timelimit} *)
val set_timelimit : float -> unit

(** Set {!val:timeout} *)
val set_timeout : (unit -> unit) -> unit

(** Set {!val:triggers_var} *)
val set_triggers_var : bool -> unit

(** Set {!val:type_smt2} *)
val set_type_smt2 : bool -> unit

(** Set {!val:unsat_core} *)
val set_unsat_core : bool -> unit

(** Set {!val:verbose} *)
val set_verbose : bool -> unit

(** Updates the filename to be parsed and sets a js_mode flag *)
val set_file_for_js : string -> unit

(** {2 Getter functions} *)

(** {3 Getters for debug flags} *)
(** Default value for all the debug flags is [false] *)

(** Get the debugging flag. *)
val debug : unit -> bool

(** Get the debugging flag of warnings. *)
val debug_warnings : unit -> bool

(** Get the debugging flag of cc. *)
val debug_cc : unit -> bool

(** Prints some debug info about the GC's activity. *)
val debug_gc : unit -> bool

(** Get the debugging flag of use. *)
val debug_use : unit -> bool

(** Get the debugging flag of uf. *)
val debug_uf : unit -> bool

(** Get the debugging flag of inequalities. *)
val debug_fm : unit -> bool

(** Get the debugging value of floating-point. *)
val debug_fpa : unit -> int
(** Default to [0]. *)

(** Get the debugging flag of Sum. *)
val debug_sum : unit -> bool

(** Get the debugging flag of ADTs. *)
val debug_adt : unit -> bool

(** Get the debugging flag of Arith (without fm). *)
val debug_arith : unit -> bool

(** Get the debugging flag of bitv. *)
val debug_bitv : unit -> bool

(** Get the debugging flag of ac. *)
val debug_ac : unit -> bool

(** Get the debugging flag of SAT. *)
val debug_sat : unit -> bool

(** Get the debugging flag of SAT (simple output). *)
val debug_sat_simple : unit -> bool

(** Get the debugging flag of typing. *)
val debug_typing : unit -> bool

(** Get the debugging flag of constructors. *)
val debug_constr : unit -> bool

(** Get the debugging flag of arrays. *)
val debug_arrays : unit -> bool

(** Get the debugging flag of ite. *)
val debug_ite : unit -> bool

(** Get the debugging flag of types. *)
val debug_types : unit -> bool

(** Get the debugging flag of combine. *)
val debug_combine : unit -> bool

(** Replay unsat-cores produced by {!val:unsat_core}.
    The option implies {!val:unsat_core} is set to [true]. *)
val debug_unsat_core : unit -> bool

(** Get the debugging flag of case-split analysis. *)
val debug_split : unit -> bool

(** Get the debugging flag of E-matching

    Possible values are
    {ol {- Disabled} {- Light} {- Full}}
*)
val debug_matching : unit -> int

(** Get the debugging flag of explanations. *)
val debug_explanations : unit -> bool

(** Get the debugging flag of triggers. *)
val debug_triggers : unit -> bool

(** Get the debugging flag for interpretation generatation. *)
val debug_interpretation : unit -> bool

(** {3 Additional getters} *)

(** {4 Case-split options} *)

(** Value specifying the case-split policy.

    Possible values are :
    {ul {- after-theory-assume} {- before-matching} {- after-matching}}

*)
val case_split_policy : unit -> Util.case_split_policy
(** Default to [after-theory-assume] *)

(** [true] if case-split for Algebraic Datatypes theory is enabled. *)
val enable_adts_cs : unit -> bool
(** Default to [false] *)

(** Value specifying the maximum size of case-split. *)
val max_split : unit -> Numbers.Q.t
(** Default to [1_000_000] *)

(** {4 Context options} *)

(** [true] if replay session will be saved in [file_name.agr]. *)
val replay : unit -> bool
(** Default to [false] *)

(** [true] if replay with all axioms and predicates saved in [.used] files
    of the current directory is enabled. *)
val replay_all_used_context : unit -> bool
(** Default to [false] *)

(** [true] if replay with axioms and predicates saved in [.used] file
    is enabled. *)
val replay_used_context : unit -> bool
(** Default to [false] *)

(** [true] if used axioms and predicates will be saved in a [.used] file.
    This option implies {!val:unsat_core} is set to [true]. *)
val save_used_context : unit -> bool
(** Default to [false] *)

(** {4 Execution options} *)

(** [true] if the locations of goals is shown when printing solver's answers. *)
val answers_with_locs  : unit -> bool
(** Default to [true] *)

(** Value of the currently selected parsing and typing frontend. *)
val frontend : unit -> string
(** Default to [legacy] *)

(** Value specifying the default input format. Useful when the extension
    does not allow to automatically select a parser (eg. JS mode, GUI
    mode, ...). *)
val input_format : unit -> string
(** Default to [.ae] *)

(** [true] if the program shall stop after parsing. *)
val parse_only : unit -> bool
(** Default to [false] *)

(** List of registered parsers for Alt-Ergo. *)
val parsers : unit -> string list
(** Default to [false] *)

(** List of files that have be loaded as preludes. *)
val preludes : unit -> string list
(** Default to [\[\]] *)

(** [true] if the program shall stop after typing. *)
val type_only : unit -> bool
(** Default to [false] *)

(** [true] if the program shall stop after SMT2 typing. *)
val type_smt2 : unit -> bool
(** Default to [false] *)

(** {4 Internal options} *)

(** [true] if the GC is prevented from collecting hashconsed data structrures
    that are not reachable (useful for more determinism). *)
val disable_weaks : unit -> bool
(** Default to [false] *)

(** [true] if verification of some heavy invariants is enabled. *)
val enable_assertions : unit -> bool
(** Default to [false] *)

(** {4 Limit options} *)

(** Value specifying the age limit bound. *)
val age_bound : unit -> int
(** Default to [50] *)

(** Value specifying the limit above which Fourier-Motzkin variables elimination
    steps that may produce a number of inequalities that is greater than this
    limit are skipped.
    However, unit eliminations are always done. *)
val fm_cross_limit : unit -> Numbers.Q.t
(** Default to [10_000] *)

(** Value specifying the maximum number of steps. *)
val steps_bound : unit -> int
(** Default to [-1] *)

(** Value specifying the time limit (not supported on Windows). *)
val timelimit : unit -> float
(** Default to [0.] *)

(** Value specifying the time limit for model generation
    (not supported on Windows). *)
val timelimit_interpretation : unit -> float
(** Default to [1.] (not supported on Windows) *)

(** Value specifying the given timelimit for each goal in case of multiple
    goals per file. In this case, time spent in preprocessing is separated from
    resolution time.

    ${i Not relevant for GUI-mode.} *)
val timelimit_per_goal : unit -> bool
(** Default to [false] *)

(** {4 Output options} *)

(** Experimental support for models on labeled terms.

    Possible values are
    {ul {- None} {- Default} {- Complete : shows a complete model}
    {- All : shows all models}}

    Which are used in the two setters below. This option answers
    [true] if the model is set to Default or Complete
*)
val model : unit -> bool
(** Default to [false] *)

(** [true] if the model is set to complete model *)
val complete_model : unit -> bool
(** Default to [false] *)

(** [true] if the model is set to all models? *)
val all_models : unit -> bool
(** Default to [false] *)

(** Experimental support for counter-example generation.

    Possible values are :
    {ol {- Unknown} {- Before instantiation}
    {- Before every decision or instantiation}}

    A negative value (-1, -2, or -3) will disable interpretation display.

    Note that {!val:max_split} limitation will be ignored in model
    generation phase. *)
val interpretation : unit -> int
(** Default to [0] *)

(** [true] if the output format is set to [Native] *)
val output_native : unit -> bool
(** Default to [true] *)

(** [true] if the output format is set to [Smtlib] *)
val output_smtlib : unit -> bool
(** Default to [false] *)

(** [true] if the output format is set to [SZS] *)
val output_szs : unit -> bool
(** Default to [false] *)

(** [true] if Alt-Ergo infers automatically the output format according to the
    input format. *)
val infer_output_format : unit -> bool
(** Default to [true] *)

(** [true] if experimental support for unsat-cores is on. *)
val unsat_core : unit -> bool
(** Default to [false] *)

(** {4 Profiling options} *)

(** [true] if the profiling module is activated.

    Use Ctrl-C to switch between different views and Ctrl + AltGr + \ to exit.
*)
val profiling : unit -> bool
(** Default to [false] *)

(** Value specifying the profiling module frequency.*)
val profiling_period : unit -> float
(** Default to [0.] *)

(** [true] if the time spent in called functions is recorded in callers *)
val cumulative_time_profiling : unit -> bool
(** Default to [false] *)

(** Value specifying which module is used as a profiling plugin. *)
val profiling_plugin : unit -> string
(** Default to [false] *)

(** [true] if profiling is set to true (automatically enabled) *)
val timers : unit -> bool
(** Default to [false] *)

(** [true] if the verbose mode is activated. *)
val verbose : unit -> bool
(** Default to [false] *)

(** {4 Quantifier options} *)

(** [true] if all available ground terms are used in instantiation. *)
val greedy : unit -> bool
(** Default to [false] *)

(** [true] if a (normal) instantiation round is made after every
    backjump/backtrack.*)
val instantiate_after_backjump : unit -> bool
(** Default to [false] *)

(** Value specifying the max number of terms allowed in multi-triggers. *)
val max_multi_triggers_size : unit -> int
(** Default to [4] *)

(** [true] if variables are allowed as triggers. *)
val triggers_var : unit -> bool
(** Default to [false] *)

(** Value specifying the number of (multi)triggers. *)
val nb_triggers : unit -> int
(** Default to [2] *)

(** [true] if matching modulo ground equalities is disabled. *)
val no_ematching : unit -> bool
(** Default to [false] *)

(** [true] if user triggers are ignored except for triggers
    of theories axioms *)
val no_user_triggers : unit -> bool
(** Default to [false] *)

(** [true] if generated substitutions are normalised by matching w.r.t.
    the state of the theory.

    This means that only terms that are greater (w.r.t. depth)
    than the initial terms of the problem are normalized. *)
val normalize_instances : unit -> bool
(** Default to [false] *)

(** {4 SAT options} *)

(** [true] if (the weak form of) matching modulo linear arithmetic
    is disabled. *)
val arith_matching : unit -> bool
(** Default to [true] *)

(** [true] if backjumping mechanism in the functional SAT solver is disabled. *)
val no_backjumping : unit -> bool
(** Default to [false] *)

(** [true] if equivalence classes at each bottom of the SAT are shown. *)
val bottom_classes : unit -> bool
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
val sat_solver : unit -> Util.sat_solver
(** Default to [CDCL-tableaux] *)

(** [true] if the use of a tableaux-like method for instantiations
    is enabled with the CDCL solver if satML is used. *)
val cdcl_tableaux_inst : unit -> bool
(** Default to [true] *)

(** [true] if the use of a tableaux-like method for theories
    is enabled with the CDCL solver if satML is used. *)
val cdcl_tableaux_th : unit -> bool
(** Default to [true] *)

(** [true] if the use of a tableaux-like method for theories or instantiations
    is enabled with the CDCL solver if satML is used. *)
val cdcl_tableaux : unit -> bool
(** Default to [true] *)

(** [true] if the tableaux SAT-solver is used with CDCL assist. *)
val tableaux_cdcl : unit -> bool
(** Default to [false] *)

(** [true] if minimal backjumping in satML CDCL solver is enabled *)
val minimal_bj : unit -> bool
(** Default to [true] *)

(** [true] if restarts are enabled for satML. *)
val enable_restarts : unit -> bool
(** Default to [false] *)

(** [true] if facts simplification is disabled in satML's flat formulas. *)
val disable_flat_formulas_simplification : unit -> bool
(** Default to [false] *)


val no_sat_learning : unit -> bool
val sat_learning : unit -> bool
(** [true] if learning/caching of unit facts in the Default SAT is disabled.
    These facts are used to improve bcp.

    Default to [true] (sat_learning is active) *)

(** Value specifying which SAT-solver is used. *)
val sat_plugin : unit -> string
(** Default to [false] *)

(** {4 Term options} *)

(** [true] if handling of ite(s) on terms in the backend is disabled. *)
val disable_ites : unit -> bool
(** Default to [false] *)

(** [true] if substitution of variables bounds by Let is enabled. The default
    behavior is to only substitute variables that are bound to a
    constant, or that appear at most once. *)
val inline_lets : unit -> bool
(** Default to [false] *)

(** [true] if rewriting is used instead of axiomatic approach. *)
val rewriting : unit -> bool
(** Default to [false] *)

(** [true] if semantic values shall be output as terms. *)
val term_like_pp : unit -> bool
(** Default to [true] *)

(** {4 Theory options} *)

(** [true] if Algebraic Datatypes theory is disabled *)
val disable_adts : unit -> bool
(** Default to [false] *)

(** Value specifying which module is used to handle inequalities
    of linear arithmetic. *)
val inequalities_plugin : unit -> string
(** Default to [false] *)

(** [true] if the AC (Associative and Commutative) theory is disabled
    for function symbols. *)
val no_ac : unit -> bool
(** Default to [false] *)

(** [true] if contracongru is disabled. *)
val no_contracongru : unit -> bool
(** Default to [false] *)

(** [true] if Fourier-Motzkin algorithm is disabled. *)
val no_fm : unit -> bool
(** Default to [false] *)

(** [true] if non-linear arithmetic reasoning (i.e. non-linear
    multplication, division and modulo on integers and rationals) is disabled.
    Non-linear multiplication remains AC. *)
val no_nla : unit -> bool
(** Default to [false] *)

(** [true] if BCP modulo theories is deactivated. *)
val no_tcp : unit -> bool
(** Default to [false] *)

(** [true] if backward reasoning step (starting from the goal) done in
    the default SAT solver before deciding is disabled. *)
val no_backward : unit -> bool
(** Default to [false] *)

(** [true] if decisions at the SAT level are disabled. *)
val no_decisions : unit -> bool
(** Default to [false] *)

(** [true] if theory reasoning is completely deactivated. *)
val no_theory : unit -> bool
(** Default to [false] *)

(** [true] if the set of decision procedures (equality, arithmetic and AC)
    is restricted. *)
val restricted : unit -> bool
(** Default to [false] *)

(** [true] if the best bounds for arithmetic variables is computed. *)
val tighten_vars : unit -> bool
(** Default to [false] *)

(** [true] if support for floating-point arithmetic is enabled. *)
val use_fpa : unit -> bool
(** Default to [false] *)

(** Possible values are
    {ul {- 0 : parsing} {- 1 : typing} {- 2 : sat} {- 3 : cc} {- 4 : arith}}

    output rules used on stderr. *)
val rules : unit -> int
(** Default to [-1] *)

(** {4 Files} *)

(** [true] if the JavaScript mode is activated *)
val js_mode : unit -> bool
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

(** Displays the used rules *)
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

val can_decide_on : string -> bool
val no_decisions_on__is_empty : unit -> bool

(** Extra *)
val set_is_gui : bool -> unit
val get_is_gui : unit -> bool

val parse_cmdline_arguments : unit -> unit
