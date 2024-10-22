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

open Format

type typing_error =
  | NonPositiveBitvType of int
  | ThExtError of string
  | ThSemTriggerError

type run_error =
  | Invalid_steps_count of int
  | Failed_check_unsat_core
  | Unsupported_feature of string
  | Dynlink_error of string
  | Stack_underflow

type mode_error =
  | Invalid_set_option of string
  | Forbidden_command of string

type model_error =
  | Subst_type_clash of Id.t * Ty.t * Ty.t
  | Subst_not_model_term of Expr.t

type error =
  | Typing_error of Loc.t * typing_error
  | Run_error of run_error
  | Warning_as_error
  | Dolmen_error of (int * string)
  | Mode_error of Util.mode * mode_error
  | Model_error of model_error

exception Error of error

let error e = raise (Error e)

let typing_error e loc =
  error (Typing_error (loc,e))

let run_error e =
  error (Run_error e)

let warning_as_error () =
  if Options.get_warning_as_error () then
    error (Warning_as_error)

let invalid_set_option mode opt_key =
  error (Mode_error (mode, Invalid_set_option opt_key))

let forbidden_command mode cmd_name =
  error (Mode_error (mode, Forbidden_command cmd_name))

let report_typing_error fmt = function
  | NonPositiveBitvType(n) ->
    fprintf fmt "non positive bitvector size (%d)" n
  | ThExtError s ->
    fprintf fmt "Theory extension %S not recognized" s
  | ThSemTriggerError ->
    fprintf fmt "Semantic triggers are only allowed inside Theories"

let report_run_error fmt = function
  | Invalid_steps_count i ->
    fprintf fmt "%d is not a valid number of steps" i
  | Failed_check_unsat_core ->
    fprintf fmt "Checking produced unsat-core failed"
  | Unsupported_feature f ->
    fprintf fmt "Unsupported Feature: %s" f
  | Dynlink_error s ->
    fprintf fmt "[Dynlink] %s" s
  | Stack_underflow ->
    fprintf fmt "The stack of the assertion levels is empty"

let report_mode_error fmt = function
  | Invalid_set_option s ->
    fprintf fmt "Set option %s" s
  | Forbidden_command s ->
    fprintf fmt "Command %s" s

let report_model_error ppf = function
  | Subst_type_clash (id, ty1, ty2) ->
    Fmt.pf ppf
      "Cannot substitute the identifier %a of type %a by an expression of \
       type %a"
      Id.pp id
      Ty.pp_smtlib ty1
      Ty.pp_smtlib ty2

  | Subst_not_model_term e ->
    Fmt.pf ppf "The expression %a is not a model term" Expr.print e

let report fmt = function
  | Typing_error (l,e) ->
    Loc.report fmt l;
    Format.fprintf fmt "Typing Error: ";
    report_typing_error fmt e
  | Run_error e ->
    Format.fprintf fmt "Fatal Error: ";
    report_run_error fmt e
  | Dolmen_error (code, descr) ->
    Format.fprintf fmt "Error %s (code %i)" descr code;
  | Warning_as_error -> ()
  | Mode_error (mode, merr) ->
    Format.fprintf
      fmt
      "Invalid action during %a mode: %a"
      Util.pp_mode mode
      report_mode_error merr;
  | Model_error err ->
    Fmt.pf fmt "Model Error: %a" report_model_error err
