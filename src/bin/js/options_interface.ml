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
open Worker_interface

let get_case_split_policy = function
  | None -> None
  | Some csp -> match csp with
    | AfterTheoryAssume -> Some Util.AfterTheoryAssume
    | BeforeMatching -> Some Util.BeforeMatching
    | AfterMatching -> Some Util.AfterMatching

let get_input_format = function
  | None -> None
  | Some f -> match f with
    | Native -> Some Options.Native
    | Smtlib2 -> Some (Options.Smtlib2 `Poly)
    | Why3 -> Some Options.Why3
    | Unknown s -> Some (Options.Unknown s)

let get_output_format = function
  | None -> None
  | Some f -> match f with
    | Native -> Some Options.Native
    | Smtlib2 -> Some (Options.Smtlib2 `Poly)
    | Why3 -> Some Options.Why3
    | Unknown s -> Some (Options.Unknown s)

let get_sat_solver = function
  | None -> None
  | Some s -> match s with
    | CDCL -> Some Util.CDCL
    | CDCL_Tableaux -> Some Util.CDCL_Tableaux
    | Tableaux -> Some Util.Tableaux
    | Tableaux_CDCL -> Some Util.Tableaux_CDCL

let get_instantiation_heuristic = function
  | None -> None
  | Some m -> match m with
    | INormal -> Some Options.INormal
    | IAuto -> Some Options.IAuto
    | IGreedy -> Some Options.IGreedy

let get_interpretation = function
  | None -> None
  | Some m -> match m with
    | INone -> Some Options.INone
    | IFirst -> Some Options.IFirst
    | IEvery -> Some Options.IEvery
    | ILast -> Some Options.ILast

let get_no_decisions_on = function
  | None -> None
  | Some l ->
    Some (List.fold_left (fun acc d ->
        Util.SS.add d acc
      ) Util.SS.empty l)

let get_frontend = function
    None -> None
  | Some f -> match f with
    | Legacy -> Some "legacy"
    | Unknown f -> Some f

let get_numbers = function
    None -> None
  | Some i -> Some (Numbers.Q.from_int i)

let set_options_opt f = function
  | None -> ()
  | Some v -> f v

let set_options r =
  set_options_opt Options.set_frontend (get_frontend r.frontend);
  set_options_opt Options.set_debug r.debug;
  set_options_opt Options.set_debug_ac r.debug_ac ;
  set_options_opt Options.set_debug_adt r.debug_adt ;
  set_options_opt Options.set_debug_arith r.debug_arith;
  set_options_opt Options.set_debug_arrays r.debug_arrays;
  set_options_opt Options.set_debug_bitv r.debug_bitv;
  set_options_opt Options.set_debug_cc r.debug_cc;
  set_options_opt Options.set_debug_combine r.debug_combine;
  set_options_opt Options.set_debug_constr r.debug_constr;
  set_options_opt Options.set_debug_explanations r.debug_explanations;
  set_options_opt Options.set_debug_fm r.debug_fm;
  set_options_opt Options.set_debug_fpa r.debug_fpa;
  set_options_opt Options.set_debug_gc r.debug_gc;
  set_options_opt Options.set_debug_interpretation r.debug_interpretation;
  set_options_opt Options.set_debug_ite r.debug_ite;
  set_options_opt Options.set_debug_matching r.debug_matching;
  set_options_opt Options.set_debug_sat r.debug_sat;
  set_options_opt Options.set_debug_split r.debug_split;
  set_options_opt Options.set_debug_triggers r.debug_triggers;
  set_options_opt Options.set_debug_types r.debug_types;
  set_options_opt Options.set_debug_uf r.debug_uf;
  set_options_opt Options.set_debug_unsat_core r.debug_unsat_core;
  set_options_opt Options.set_debug_use r.debug_use;
  set_options_opt Options.set_debug_warnings r.debug_warnings;
  set_options_opt Options.set_rule r.rule;

  set_options_opt Options.set_case_split_policy
    (get_case_split_policy r.case_split_policy);
  set_options_opt Options.set_enable_adts_cs r.enable_adts_cs;
  set_options_opt Options.set_max_split (get_numbers r.max_split);

  set_options_opt Options.set_replay r.replay;
  set_options_opt Options.set_replay_all_used_context
    r.replay_all_used_context;
  set_options_opt Options.set_replay_used_context r.replay_used_context;
  set_options_opt Options.set_save_used_context r.save_used_context;

  set_options_opt Options.set_answers_with_loc r.answers_with_loc;
  Options.set_input_format (get_input_format r.input_format);
  set_options_opt Options.set_parse_only r.parse_only;
  set_options_opt Options.set_preludes r.preludes;
  set_options_opt Options.set_type_only r.type_only;
  set_options_opt Options.set_type_smt2 r.type_smt2;

  set_options_opt Options.set_disable_weaks r.disable_weaks;
  set_options_opt Options.set_enable_assertions r.enable_assertions;

  set_options_opt Options.set_age_bound r.age_bound;
  set_options_opt Options.set_fm_cross_limit (get_numbers r.fm_cross_limit);
  set_options_opt Options.set_steps_bound r.steps_bound;

  set_options_opt Options.set_interpretation
    (get_interpretation r.interpretation);

  set_options_opt Options.set_output_format
    (get_output_format r.output_format);
  Options.set_infer_output_format
    (get_input_format r.output_format |> Option.is_none);
  set_options_opt Options.set_unsat_core r.unsat_core;

  set_options_opt Options.set_verbose r.verbose;

  set_options_opt Options.set_instantiation_heuristic
    (get_instantiation_heuristic r.instantiation_heuristic);
  set_options_opt Options.set_instantiate_after_backjump
    r.instantiate_after_backjump;
  set_options_opt Options.set_max_multi_triggers_size r.max_multi_triggers_size;
  set_options_opt Options.set_nb_triggers r.nb_triggers;
  set_options_opt Options.set_no_ematching r.no_ematching;
  set_options_opt Options.set_no_user_triggers r.no_user_triggers;
  set_options_opt Options.set_normalize_instances r.normalize_instances;
  set_options_opt Options.set_triggers_var r.triggers_var;

  set_options_opt Options.set_arith_matching r.arith_matching;
  set_options_opt Options.set_bottom_classes r.bottom_classes;
  set_options_opt Options.set_cdcl_tableaux_inst r.cdcl_tableaux_inst;
  set_options_opt Options.set_cdcl_tableaux_th r.cdcl_tableaux_th;
  set_options_opt Options.set_disable_flat_formulas_simplification
    r.disable_flat_formulas_simplification;
  set_options_opt Options.set_enable_restarts r.enable_restarts;
  set_options_opt Options.set_minimal_bj r.minimal_bj;
  set_options_opt Options.set_no_backjumping r.no_backjumping;
  set_options_opt Options.set_no_backward r.no_backward;
  set_options_opt Options.set_no_decisions r.no_decisions;
  set_options_opt Options.set_no_decisions_on
    (get_no_decisions_on r.no_decisions_on);
  set_options_opt Options.set_no_sat_learning r.no_sat_learning;
  set_options_opt Options.set_sat_solver (get_sat_solver r.sat_solver);

  set_options_opt Options.set_disable_ites r.disable_ites;
  set_options_opt Options.set_inline_lets r.inline_lets;
  set_options_opt Options.set_rewriting r.rewriting;
  set_options_opt Options.set_term_like_pp r.term_like_pp;

  set_options_opt Options.set_disable_adts r.disable_adts;
  set_options_opt Options.set_no_ac r.no_ac;
  set_options_opt Options.set_no_contracongru r.no_contracongru;
  set_options_opt Options.set_no_fm r.no_fm;
  set_options_opt Options.set_no_nla r.no_nla;
  set_options_opt Options.set_no_tcp r.no_tcp;
  set_options_opt Options.set_no_theory r.no_theory;
  set_options_opt Options.set_restricted r.restricted;
  set_options_opt Options.set_tighten_vars r.tighten_vars;
  set_options_opt Options.set_timers r.timers;

  set_options_opt Options.set_file r.file;
