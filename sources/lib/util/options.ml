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

let fmt = Format.err_formatter

module M = struct

  let file = ref ""
  let session_file = ref ""
  let used_context_file = ref ""
  let rewriting = ref false
  let type_only = ref false
  let type_smt2 = ref false
  let parse_only = ref false
  let frontend = ref "legacy"
  let steps_bound = ref (-1)
  let age_bound = ref 50
  let debug = ref false
  let debug_warnings = ref false
  let no_user_triggers = ref false
  let debug_triggers = ref false
  let debug_cc = ref false
  let debug_gc = ref false
  let debug_use = ref false
  let debug_arrays = ref false
  let debug_ite = ref false
  let debug_uf = ref false
  let debug_sat = ref false
  let debug_sat_simple = ref false
  let debug_typing = ref false
  let debug_constr = ref false
  let verbose = ref false
  let debug_fm = ref false
  let debug_fpa = ref 0
  let debug_sum = ref false
  let debug_adt = ref false
  let debug_arith = ref false
  let debug_combine = ref false
  let debug_bitv = ref false
  let debug_ac = ref false
  let debug_split = ref false
  (* unused -- let options = ref false *)
  let greedy = ref false
  let disable_ites = ref false
  let disable_adts = ref false
  let enable_adts_cs = ref false
  let triggers_var = ref false
  let nb_triggers = ref 2
  let max_multi_triggers_size = ref 4
  let enable_assertions = ref false
  let no_Ematching = ref false
  let arith_matching = ref true
  let no_backjumping = ref false
  let nocontracongru = ref false
  let term_like_pp = ref true
  let debug_types = ref false
  let all_models = ref false
  let model = ref false
  let complete_model = ref false
  let interpretation = ref 0
  let debug_interpretation = ref false
  let unsat_core = ref false
  let debug_unsat_core = ref false
  let rules = ref (-1)
  let max_split = ref (Numbers.Q.from_int 1000000)
  let fm_cross_limit = ref (Numbers.Q.from_int 10_000)
  let case_split_policy = ref Util.AfterTheoryAssume
  let restricted = ref false
  let bottom_classes = ref false
  let timelimit = ref 0.
  let timelimit_per_goal = ref false
  let interpretation_timelimit = ref (if Sys.win32 then 0. else 1.)
  let debug_matching = ref 0
  let debug_explanations = ref false
  let sat_plugin = ref ""
  let parsers = ref []
  let inequalities_plugin = ref ""
  let profiling_plugin = ref ""
  let cumulative_time_profiling = ref false
  let normalize_instances = ref false

  let sat_solver = ref Util.CDCL_Tableaux
  let cdcl_tableaux_inst = ref true
  let cdcl_tableaux_th = ref true
  let tableaux_cdcl = ref false
  let minimal_bj = ref true
  let enable_restarts = ref false
  let disable_flat_formulas_simplification = ref false

  let tighten_vars = ref false
  let no_tcp = ref false
  let no_decisions = ref false

  let no_decisions_on = ref Util.SS.empty
  let no_fm = ref false
  let no_theory = ref false
  let js_mode = ref false
  let use_fpa = ref false
  let reversed_preludes : string list ref = ref []
  let no_NLA = ref false
  let no_ac = ref false
  let no_backward = ref false
  let no_sat_learning = ref false
  let instantiate_after_backjump = ref false
  let disable_weaks = ref false
  let default_input_lang = ref ".why"
  let no_locs_in_answers = ref false

  let unsat_mode = ref false
  let inline_lets = ref false

  let show_where s=
    match s with
    | "" -> ()
    | s ->
      let path = match s with
        | "lib" -> Config.libdir
        | "plugins" -> Config.pluginsdir
        | "preludes" -> Config.preludesdir
        | "data" -> Config.datadir
        | "man" -> Config.mandir
        | s -> raise (Arg.Bad ("Option -where has no argument " ^ s))
      in
      Format.printf "%s@." path; exit 0

  let show_version () = Format.printf "%s@." Version._version; exit 0

  let show_version_info () =
    Format.printf "Version          = %s@." Version._version;
    Format.printf "Release date     = %s@." Version._release_date;
    Format.printf "Release commit   = %s@." Version._release_commit;
    exit 0

  let set_max_split s =
    max_split :=
      try Numbers.Q.from_string s
      with Failure _ -> Numbers.Q.m_one

  let set_fm_cross_limit s =
    fm_cross_limit :=
      try Numbers.Q.from_string s
      with Failure _ -> Numbers.Q.m_one


  let update_no_decisions_on s =
    no_decisions_on :=
      List.fold_left
        (fun set s ->
           match s with
           | "" -> set
           | s -> Util.SS.add s set
        ) !no_decisions_on (Str.split (Str.regexp ",") s)

  let set_sat_plugin s = sat_plugin := s

  let add_parser p = parsers := p :: !parsers

  let set_inequalities_plugin s = inequalities_plugin := s

  let set_profiling_plugin s = profiling_plugin := s

  (* unused -- let set_unsat_core b = unsat_core := b *)

  let set_rules = function
    | "parsing" -> rules := 0
    | "typing" -> rules := 1
    | "sat" -> rules := 2
    | "cc" -> rules := 3
    | "arith" -> rules := 4
    | _ -> rules := -1

  let set_limit timelimit_target t =
    if Sys.win32 then
      Format.eprintf "timelimit not supported on Win32 (ignored)@."
    else
      timelimit_target := t

  let replay = ref false
  let replay_used_context = ref false
  let replay_all_used_context = ref false
  let save_used_context = ref false

  let profiling_period = ref 0.
  let profiling = ref false

  let parse_profiling s =
    profiling := true;
    try profiling_period := float_of_string s
    with _ -> ()

  let set_case_split_policy_option s =
    case_split_policy :=
      match s with
      | "after-theory-assume" -> Util.AfterTheoryAssume
      | "before-matching" -> Util.BeforeMatching
      | "after-matching" -> Util.AfterMatching
      | _ -> raise (Arg.Bad ("Bad value '"^s^"' for option -case-split-policy"))

  let add_prelude p =
    reversed_preludes := p :: !reversed_preludes

  let set_default_input_lang lang = default_input_lang := "." ^ lang

  let set_steps_bounds n =
    if n >= 0 then steps_bound := n
    else
      raise (Arg.Bad ("-steps-bound argument should be positive"))

  let timers = ref false

  let usage = "usage: alt-ergo [options] file.<why|mlw>"

  let set_sat_solver s =
    match s with
    | "CDCL" | "satML" ->
      sat_solver := Util.CDCL;
      cdcl_tableaux_inst := false;
      cdcl_tableaux_th := false
    | "CDCL-Tableaux" | "satML-Tableaux" | "CDCL-tableaux" | "satML-tableaux" ->
      sat_solver := Util.CDCL_Tableaux;
      cdcl_tableaux_inst := true;
      cdcl_tableaux_th := true
    | "tableaux" | "Tableaux" | "tableaux-like" | "Tableaux-like" ->
      sat_solver := Util.Tableaux;
      tableaux_cdcl := false
    | "tableaux-cdcl" | "Tableaux-CDCL" | "tableaux-CDCL" | "Tableaux-cdcl" ->
      sat_solver := Util.Tableaux_CDCL;
      tableaux_cdcl := true;
    | _ ->
      Format.eprintf "Args parsing error: unkown SAT solver %S@." s;
      exit 1

  let spec = [
    "-parse-only",
    Arg.Set parse_only,
    " stop after parsing";

    "-frontend",
    Arg.Set_string frontend,
    " select the parsing and typing frontend";

    "-type-only",
    Arg.Set type_only,
    " stop after typing";

    "-type-smt2",
    Arg.Set type_smt2,
    " stop after smt2 typing";

    "-no-user-triggers",
    Arg.Set no_user_triggers,
    " ignore user triggers, except for triggers of theories axioms";

    "-debug",
    Arg.Set debug,
    "  sets the debugging flag";

    "-dwarnings",
    Arg.Set debug_warnings,
    "  sets the debugging flag of warnings";

    "-dcc",
    Arg.Set debug_cc,
    "  sets the debugging flag of cc";

    "-dgc",
    Arg.Set debug_gc,
    "  prints some debug info about the GC's activity";

    "-duse",
    Arg.Set debug_use,
    "  sets the debugging flag of use";

    "-duf",
    Arg.Set debug_uf,
    "  sets the debugging flag of uf";

    "-dfm",
    Arg.Set debug_fm,
    "  sets the debugging flag of inequalities";

    "-dfpa",
    Arg.Set_int debug_fpa,
    "  sets the debugging flag of floating-point";

    "-dsum",
    Arg.Set debug_sum,
    "  sets the debugging flag of Sum";

    "-dadt",
    Arg.Set debug_adt,
    "  sets the debugging flag of ADTs";

    "-darith",
    Arg.Set debug_arith,
    " sets the debugging flag of Arith (without fm)";

    "-dbitv",
    Arg.Set debug_bitv,
    "  sets the debugging flag of bitv";

    "-dac",
    Arg.Set debug_ac,
    "  sets the debugging flag of ac";

    "-dsat",
    Arg.Set debug_sat,
    "  sets the debugging flag of sat";

    "-dsats",
    Arg.Set debug_sat_simple,
    "  sets the debugging flag of sat (simple output)";

    "-dtyping",
    Arg.Set debug_typing,
    "  sets the debugging flag of typing";

    "-types",
    Arg.Set debug_types,
    "  sets the debugging flag of types";

    "-dconstr",
    Arg.Set debug_constr,
    "  sets the debugging flag of constructors";

    "-darrays",
    Arg.Set debug_arrays,
    "  sets the debugging flag of arrays";

    "-dite",
    Arg.Set debug_ite,
    "  sets the debugging flag of ite";

    "-dcombine",
    Arg.Set debug_combine,
    "  sets the debugging flag of combine";

    "-dsplit",
    Arg.Set debug_split,
    "  sets the debugging flag of case-split analysis";

    "-dmatching",
    Arg.Set_int debug_matching,
    "  sets the debugging flag of E-matching (0=disabled, 1=light, 2=full)";

    "-dexplanations",
    Arg.Set debug_explanations,
    "  sets the debugging flag of explanations";

    "-dtriggers",
    Arg.Set debug_triggers,
    "  sets the debugging flag of triggers";

    "-verbose",
    Arg.Set verbose,
    "  sets the verbose mode";

    "-version",
    Arg.Unit show_version,
    "  prints the version number";

    "-version-info",
    Arg.Unit show_version_info,
    "  prints some info about this version";

    "-where",
    Arg.String show_where,
    "  prints the directory of its argument. Possible arguments are: \
     'lib', 'plugins', 'preludes', 'data' and 'man'";

    "-disable-ites",
    Arg.Set disable_ites,
    "  disable handling of ite(s) on terms in the backend";

    "-disable-adts",
    Arg.Set disable_adts,
    "  disable Algebraic Datatypes theory";

    "-enable-adts-cs",
    Arg.Set enable_adts_cs,
    "  enable case-split for Algebraic Datatypes theory";

    "-steps-bound",
    Arg.Int set_steps_bounds,
    " <n> set the maximum number of steps";

    "-enable-assertions",
    Arg.Set enable_assertions,
    " Enable verification of some heavy invariants";

    "-no-tcp",
    Arg.Set no_tcp,
    " Deactivate BCP modulo theories";

    "-no-decisions",
    Arg.Set no_decisions,
    " Disable decisions at the SAT level";

    "-no-decisions-on",
    Arg.String update_no_decisions_on,
    " Disable decisions at the SAT level for the instances generated \
     from the given axioms. Arguments should be separated with a comma";

    "-no-fm",
    Arg.Set no_fm,
    " Disable Fourier-Motzkin algorithm";

    "-tighten-vars",
    Arg.Set tighten_vars,
    " Compute the best bounds for arithmetic variables";

    "-no-theory",
    Arg.Set no_theory,
    " Completely deactivate theory reasoning";

    "-age-bound",
    Arg.Set_int age_bound,
    "<n> set the age limite bound";

    "-greedy" ,
    Arg.Set greedy,
    " use all available ground terms in instantiation";

    "-nb-triggers" ,
    Arg.Set_int nb_triggers,
    " number of (multi)triggers (default: 2)";

    "-max-multi-triggers-size" ,
    Arg.Set_int max_multi_triggers_size,
    " max number of terms allowed in multi-triggers (default: 4)";

    "-triggers-var" ,
    Arg.Set triggers_var ,
    " allows variables as triggers";

    "-no-Ematching",
    Arg.Set no_Ematching,
    " disable matching modulo ground equalities";

    "-no-arith-matching",
    Arg.Clear arith_matching,
    " disable (the weak form of) matching modulo linear arithmetic";

    "-no-backjumping",
    Arg.Set no_backjumping,
    " disable backjumping mechanism in the functional SAT solver";

    "-no-NLA",
    Arg.Set no_NLA,
    " disable non-linear arithmetic reasoning (i.e. non-linear \
     multplication, division and modulo on integers and rationals). \
     Non-linear multiplication remains AC";

    "-no-ac",
    Arg.Set no_ac,
    " Disable the AC theory of Associative and Commutative function symbols";

    "-nocontracongru",
    Arg.Set nocontracongru,
    "";

    "-term-like-pp",
    Arg.Set term_like_pp,
    " output semantic values as terms";

    "-all-models",
    Arg.Set all_models,
    " experimental support for all models";

    "-model",
    Arg.Set model,
    " experimental support for models on labeled terms";

    "-complete-model",
    Arg.Set complete_model,
    " experimental support for complete model";

    "-dinterpretation",
    Arg.Set debug_interpretation,
    " set debug flag for interpretation generatation";

    "-interpretation",
    Arg.Set_int interpretation,
    " experimental support for counter-example generation. Possible values \
     are 1, 2, or 3 to compute an interpretation before returning Unknown, \
     before instantiation, or before every decision or instantiation. \
     A negative value (-1, -2, or -3) will disable interpretation display. \
     Note that -max-split limitation will be ignored in model generation phase";

    "-unsat-core",
    Arg.Set unsat_core,
    " experimental support for unsat-cores";

    "-debug-unsat-core",
    Arg.Set debug_unsat_core,
    " replay unsat-cores produced by -unsat-core. The option implies \
     -unsat-core";

    "-rules",
    Arg.String set_rules,
    "tr (tr in <parsing|typing|sat|cc|arith>) output rules used on stderr";

    "-max-split",
    Arg.String set_max_split,
    (Format.sprintf " maximum size of case-split (default value : %s)"
       (Numbers.Q.to_string !max_split));


    "-fm-cross-limit",
    Arg.String set_fm_cross_limit,
    (Format.sprintf
       " skip Fourier-Motzkin variables elimination steps that may produce \
        a number of inequalities that is greater than the given limit \
        (default value : %s). However, unit eliminations are always done"
       (Numbers.Q.to_string !fm_cross_limit));

    "-case-split-policy",
    Arg.String set_case_split_policy_option,
    " case-split policy. Set the case-split policy to use. Possible values \
     are: after-theory-assume (default), before-matching, after-matching";

    "-restricted",
    Arg.Set restricted,
    " restrict set of decision procedures (equality, arithmetic and AC)";

    "-bottom-classes",
    Arg.Set bottom_classes,
    " show equivalence classes at each bottom of the sat";

    "-replay",
    Arg.Set replay,
    " replay session saved in .agr";

    "-replay-used-context",
    Arg.Set replay_used_context,
    " replay with axioms and predicates saved in .used file";

    "-replay-all-used-context",
    Arg.Set replay_all_used_context,
    " replay with all axioms and predicates saved in .used files of the \
     current directory";

    "-save-used-context",
    Arg.Set save_used_context,
    " save used axioms and predicates in a .used file. This option implies \
     -unsat-core";

    "-timelimit",
    Arg.Float (set_limit timelimit),
    "n set the time limit to n seconds (not supported on Windows)";

    "-timelimit-per-goal",
    Arg.Set timelimit_per_goal,
    " Set the given timelimit for each goal, in case of multiple goals per \
     file. In this case, time spent in preprocessing is separated from \
     resolution time. Not relevant for GUI-mode.";

    "-interpretation-timelimit",
    Arg.Float (set_limit interpretation_timelimit),
    "n set the time limit to n seconds for model generation (not supported \
     on Windows). Default value is 1. sec";

    "-sat-plugin" ,
    Arg.String set_sat_plugin,
    " use the given SAT-solver instead of the default DFS-based SAT solver";

    "-sat-solver" ,
    Arg.String set_sat_solver,
    " choose the SAT solver to use. Default value is CDCL (i.e. satML \
     solver). value 'Tableaux' will enable the Tableaux-like solver";

    "-no-minimal-bj" ,
    Arg.Clear minimal_bj,
    " disable minimal backjumping in satML CDCL solver";

    "-no-tableaux-cdcl-in-instantiation",
    Arg.Clear cdcl_tableaux_inst,
    " when satML is used, this disables the use of a tableaux-like method \
     for instantiations with the CDCL solver";

    "-no-tableaux-cdcl-in-theories",
    Arg.Clear cdcl_tableaux_th,
    " when satML is used, this disables the use of a tableaux-like method \
     for the theories with the CDCL solver";

    "-disable-flat-formulas-simplification",
    Arg.Set disable_flat_formulas_simplification,
    " disable facts simplifications in satML's flat formulas";

    "-inequalities-plugin" ,
    Arg.String set_inequalities_plugin,
    " use the given module to handle inequalities of linear arithmetic";

    "-parser" ,
    Arg.String add_parser,
    " register a new parser for Alt-Ergo";

    "-profiling",
    Arg.String parse_profiling,
    "<delay> activate the profiling module with the given frequency. \
     Use Ctrl-C to switch between different views and \"Ctrl + AltGr + \\\" \
     to exit.";

    "-profiling-plugin" ,
    Arg.String set_profiling_plugin,
    " use the given profiling plugin";

    "-cumulative-time-profiling",
    Arg.Set cumulative_time_profiling,
    " the time spent in called functions is also recorded in callers";

    "-rwt",
    Arg.Set rewriting,
    " use rewriting instead of axiomatic approach";

    "-normalize-instances" ,
    Arg.Set normalize_instances,
    " normalize generated substitutions by matching w.r.t. the state of \
     the theory. Default value is false. This means that only terms that \
     are greater (w.r.t. depth) than the initial terms of the problem are \
     normalized.";

    "-use-fpa",
    Arg.Set use_fpa,
    " enable support for floating-point arithmetic";

    "-prelude",
    Arg.String add_prelude,
    " add a file that will be loaded as a prelude. The command is \
     cumulative, and the order of successive preludes is presrved.";

    "-inst-after-bj",
    Arg.Set instantiate_after_backjump,
    " make a (normal) instantiation round after every backjump/backtrack";

    "-no-backward",
    Arg.Set no_backward,
    " Disable backward reasoning step (starting from the goal) done in \
     the default SAT solver before deciding";

    "-no-sat-learning",
    Arg.Set no_sat_learning,
    " Disable learning/caching of unit facts in the Default SAT. These \
     facts are used to improve bcp";

    "-disable-weaks",
    Arg.Set disable_weaks,
    " Prevent the GC from collecting hashconsed data structrures that are \
     not reachable (useful for more determinism)";

    "-enable-restarts",
    Arg.Set enable_restarts,
    " For satML: enable restarts or not. Default behavior is 'false'";

    "-default-lang",
    Arg.String set_default_input_lang,
    " Set the default input language to 'lang'. Useful when the extension \
     does not allow to automatically select a parser (eg. JS mode, GUI \
     mode, ...)";

    "-no-locs-in-answers",
    Arg.Set no_locs_in_answers,
    " Do not show the locations of goals when printing solver's answers.";

    "-unsat-mode",
    Arg.Set unsat_mode,
    " answer unsat / sat / unknown instead of Valid / Invalid / I don't know";

    "-inline-lets",
    Arg.Set inline_lets,
    " enable substutition of variables bounds by Let. The default \
     behavior is to only substitute variables that are bound to a \
     constant, or that appear at most once."

  ]

  let spec =
    List.fast_sort (fun (s1,_,_) (s2,_,_) -> String.compare s1 s2) spec

  let spec = Arg.align spec

  let thread_yield = ref (fun () -> ())

  let (timeout : (unit -> unit) ref) =
    ref (fun () -> raise Util.Timeout)

end

let parse_cmdline_arguments () =
  let ofile = ref None in
  let set_file s = ofile := Some s in
  Arg.parse M.spec set_file M.usage;
  match !ofile with
  | Some f ->
    M.file := f;
    let base_file = Filename.chop_extension f in
    M.session_file := base_file^".agr";
    M.used_context_file := base_file
  | None -> ()


let set_file_for_js filename =
  M.file := filename;
  M.js_mode := true

(** setter functions **********************************************************)

(** setters for debug flags *)
let set_debug b = M.debug := b
let set_debug_cc b = M.debug_cc := b
let set_debug_gc b = M.debug_gc := b
let set_debug_use b = M.debug_use := b
let set_debug_uf b = M.debug_uf := b
let set_debug_fm b = M.debug_fm := b
let set_debug_sum b = M.debug_sum := b
let set_debug_adt b = M.debug_adt := b
let set_debug_arith b = M.debug_arith := b
let set_debug_bitv b = M.debug_bitv := b
let set_debug_ac   b = M.debug_ac := b
let set_debug_sat b = M.debug_sat := b
let set_debug_sat_simple b = M.debug_sat_simple := b
let set_debug_typing b = M.debug_typing := b
let set_debug_constr b = M.debug_constr := b
let set_debug_arrays b = M.debug_arrays := b
let set_debug_ite b = M.debug_ite := b
let set_debug_types b = M.debug_types := b
let set_debug_combine b = M.debug_combine := b
let set_debug_unsat_core b = M.debug_unsat_core := b
let set_debug_split b = M.debug_split := b
let set_debug_matching i = M.debug_matching := i
let set_debug_explanations b = M.debug_explanations := b

(** additional setters *)
let set_type_only b = M.type_only := b
let set_type_smt2 b = M.type_smt2 := b
let set_parse_only b = M.parse_only := b
let set_frontend s = M.frontend := s
let set_age_bound b = M.age_bound := b
let set_no_user_triggers b = M.no_user_triggers := b
let set_verbose b = M.verbose := b
let set_greedy b = M.greedy := b
let set_triggers_var b = M.triggers_var := b
let set_nb_triggers b = M.nb_triggers := b
let set_no_Ematching b = M.no_Ematching := b
let set_no_NLA b = M.no_NLA := b
let set_no_ac b = M.no_ac := b
let set_normalize_instances b = M.normalize_instances := b
let set_steps_bound b = M.steps_bound := b
let set_nocontracongru b = M.nocontracongru := b
let set_term_like_pp b = M.term_like_pp := b
let set_all_models b = M.all_models := b
let set_model b = M.model := b
let set_complete_model b = M.complete_model := b
let set_interpretation b = M.interpretation := b
let set_max_split b = M.max_split := b
let set_fm_cross_limit b = M.fm_cross_limit := b
let set_rewriting b = M.rewriting := b
let set_unsat_core b = M.unsat_core := b
let set_rules b = M.rules := b
let set_restricted b = M.restricted := b
let set_bottom_classes b = M.bottom_classes := b
let set_timelimit b = M.timelimit := b
(* unused -- let set_model_timelimit b = M.timelimit := b *)
let set_timers b = M.timers := b
(* unused -- let set_minimal_bj b = M.minimal_bj := b *)

let set_profiling f b =
  M.profiling := b;
  M.profiling_period := if b then f else 0.

let set_thread_yield f = M.thread_yield := f
let set_timeout f = M.timeout := f
let set_save_used_context b = M.save_used_context := b
let set_default_input_lang lang = M.set_default_input_lang lang
let set_unsat_mode b = M.unsat_mode := b
let set_inline_lets m = M.inline_lets := m

(** getter functions **********************************************************)

(** getters for debug flags *)
let debug () = !M.debug
let debug_warnings () = !M.debug_warnings
let debug_cc () = !M.debug_cc
let debug_gc () = !M.debug_gc
let debug_use () = !M.debug_use
let debug_uf () = !M.debug_uf
let debug_fm () = !M.debug_fm
let debug_fpa () = !M.debug_fpa
let debug_sum () = !M.debug_sum
let debug_adt () = !M.debug_adt
let debug_arith () = !M.debug_arith
let debug_bitv () = !M.debug_bitv
let debug_ac   () = !M.debug_ac
let debug_sat () = !M.debug_sat
let debug_sat_simple () = !M.debug_sat_simple
let debug_typing () = !M.debug_typing
let debug_constr () = !M.debug_constr
let debug_arrays () = !M.debug_arrays
let debug_ite () = !M.debug_ite
let debug_types () = !M.debug_types
let debug_combine () = !M.debug_combine
let debug_unsat_core () = !M.debug_unsat_core
let debug_split () = !M.debug_split
let debug_matching () = !M.debug_matching
let debug_explanations () = !M.debug_explanations
let debug_triggers () = !M.debug_triggers

(** additional getters *)
let disable_ites () = !M.disable_ites
let disable_adts () = !M.disable_adts
let enable_adts_cs () = !M.enable_adts_cs
let js_mode () = !M.js_mode
let type_only () = !M.type_only
let type_smt2 () = !M.type_smt2
let parse_only () = !M.parse_only
let frontend () = !M.frontend
let steps_bound () = !M.steps_bound
let no_tcp () = !M.no_tcp
let no_decisions () = !M.no_decisions
let no_fm () = !M.no_fm
let no_theory () = !M.no_theory
let tighten_vars () = !M.tighten_vars
let age_bound () = !M.age_bound
let no_user_triggers () = !M.no_user_triggers
let verbose () = !M.verbose
let greedy () = !M.greedy
let triggers_var () = !M.triggers_var
let nb_triggers () = !M.nb_triggers
let max_multi_triggers_size () = !M.max_multi_triggers_size
let no_Ematching () = !M.no_Ematching
let arith_matching () = !M.arith_matching
let no_backjumping () = !M.no_backjumping
let no_NLA () = !M.no_NLA
let no_ac () = !M.no_ac
let no_backward () = !M.no_backward
let no_sat_learning () = !M.no_sat_learning
let sat_learning () = not !M.no_sat_learning
let nocontracongru () = !M.nocontracongru
let term_like_pp () = !M.term_like_pp
let cumulative_time_profiling () = !M.cumulative_time_profiling
let all_models () = !M.all_models
let model () = !M.model || !M.complete_model
let interpretation () = !M.interpretation
let debug_interpretation () = !M.debug_interpretation
let complete_model () = !M.complete_model
let max_split () = !M.max_split
let fm_cross_limit () = !M.fm_cross_limit
let rewriting () = !M.rewriting
let unsat_core () = !M.unsat_core || !M.save_used_context || !M.debug_unsat_core
let rules () = !M.rules
let restricted () = !M.restricted
let bottom_classes () = !M.bottom_classes
let timelimit () = !M.timelimit
let timelimit_per_goal () = !M.timelimit_per_goal
let interpretation_timelimit () = !M.interpretation_timelimit
let enable_assertions () = !M.enable_assertions
let profiling () =  !M.profiling
let profiling_period () = !M.profiling_period
let timers () = !M.timers || !M.profiling
let case_split_policy () = !M.case_split_policy
let instantiate_after_backjump () = !M.instantiate_after_backjump
let disable_weaks () = !M.disable_weaks
let minimal_bj () = !M.minimal_bj
let cdcl_tableaux_inst () = !M.cdcl_tableaux_inst
let cdcl_tableaux_th () = !M.cdcl_tableaux_th
let cdcl_tableaux () = !M.cdcl_tableaux_th || !M.cdcl_tableaux_inst
let tableaux_cdcl () = !M.tableaux_cdcl
let disable_flat_formulas_simplification () =
  !M.disable_flat_formulas_simplification

let enable_restarts () = !M.enable_restarts

let replay () = !M.replay
let replay_used_context () = !M.replay_used_context
let replay_all_used_context () = !M.replay_all_used_context
let save_used_context () = !M.save_used_context
let get_file () = !M.file
let get_session_file () = !M.session_file
let get_used_context_file () = !M.used_context_file
let sat_plugin () = !M.sat_plugin
let parsers () = List.rev !M.parsers
let sat_solver () = !M.sat_solver
let inequalities_plugin () = !M.inequalities_plugin
let profiling_plugin () = !M.profiling_plugin
let normalize_instances () = !M.normalize_instances
let use_fpa () = !M.use_fpa
let preludes () = List.rev !M.reversed_preludes

let can_decide_on s =
  !M.no_decisions_on == Util.SS.empty || not (Util.SS.mem s !M.no_decisions_on)

let no_decisions_on__is_empty () = !M.no_decisions_on == Util.SS.empty

let default_input_lang () = !M.default_input_lang
let answers_with_locs ()  = not !M.no_locs_in_answers
let unsat_mode ()  = !M.unsat_mode
let inline_lets () = !M.inline_lets

(** particular getters : functions that are immediately executed **************)
let exec_thread_yield () = !M.thread_yield ()
let exec_timeout () = !M.timeout ()

let tool_req n msg =
  if rules () = n then Format.fprintf fmt "[rule] %s@." msg


(** Simple Timer module **)
module Time = struct

  let u = ref 0.0

  let start () =
    u := MyUnix.cur_time()

  let value () =
    MyUnix.cur_time() -. !u

  let set_timeout ~is_gui tm = MyUnix.set_timeout ~is_gui tm

  let unset_timeout ~is_gui =
    if timelimit() <> 0. then
      MyUnix.unset_timeout ~is_gui

end

(** globals **)
let cs_steps_cpt = ref 0
let cs_steps () = !cs_steps_cpt
let incr_cs_steps () = incr cs_steps_cpt

let steps = ref 0
let get_steps () = !steps
let reset_steps () = steps := 0
let incr_and_check_steps cpt =
  if cpt < 0 then
    begin
      Format.eprintf "Steps can only be positive@.";
      exit 1
    end;
  steps := !steps + cpt;
  if steps_bound () <> (-1) && (0 > !steps || !steps >= steps_bound ()) then
    begin
      Format.eprintf "Steps limit reached: %d@."
        (if !steps > 0 then !steps else
           steps_bound ());
      exit 1
    end


(** open Options in every module to hide polymorphic versions of Pervasives **)
let (<>) (a: int) (b: int) = a <> b
let (=)  (a: int) (b: int) = a = b
let (<)  (a: int) (b: int) = a < b
let (>)  (a: int) (b: int) = a > b
let (<=) (a: int) (b: int) = a <= b
let (>=) (a: int) (b: int) = a >= b

let compare  (a: int) (b: int) = Pervasives.compare a b


(* extra **)

let is_gui = ref None

let set_is_gui b =
  match !is_gui with
  | None -> is_gui := Some b
  | Some _ ->
    Format.eprintf "Error in Options.set_is_gui: is_gui is already set!@.";
    assert false

let get_is_gui () =
  match !is_gui with
  | Some b -> b
  | None ->
    Format.eprintf "Error in Options.get_is_gui: is_gui is not set!@.";
    assert false

