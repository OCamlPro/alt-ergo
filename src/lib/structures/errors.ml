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
  | BitvExtract of int*int
  | BitvExtractRange of int*int
  | NonPositiveBitvType of int
  | ClashType of string
  | ClashLabel of string * string
  | ClashParam of string
  | TypeDuplicateVar of string
  | UnboundedVar of string
  | UnknownType of string
  | WrongArity of string * int
  | SymbAlreadyDefined of string
  | SymbUndefined of string
  | NotAPropVar of string
  | NotAPredicate of string
  | Unification of Ty.t * Ty.t
  | ShouldBeApply of string
  | WrongNumberofArgs of string
  | ShouldHaveType of Ty.t * Ty.t
  | ShouldHaveTypeIntorReal of Ty.t
  | ShouldHaveTypeInt of Ty.t
  | ShouldHaveTypeBitv of Ty.t
  | ArrayIndexShouldHaveTypeInt
  | ShouldHaveTypeArray
  | ShouldHaveTypeRecord of Ty.t
  | ShouldBeARecord
  | ShouldHaveLabel of string * string
  | NoLabelInType of Hstring.t * Ty.t
  | ShouldHaveTypeProp
  | NoRecordType of Hstring.t
  | DuplicateLabel of Hstring.t
  | DuplicatePattern of string
  | WrongLabel of Hstring.t * Ty.t
  | WrongNumberOfLabels
  | Notrigger
  | CannotGeneralize
  | SyntaxError
  | ThExtError of string
  | ThSemTriggerError
  | WrongDeclInTheory
  | ShouldBeADT of Ty.t
  | MatchNotExhaustive of Hstring.t list
  | MatchUnusedCases of Hstring.t list
  | NotAdtConstr of string * Ty.t
  | BadPopCommand of {pushed : int; to_pop : int}
  | ShouldBePositive of int
  | PolymorphicEnum of string
  | ShouldBeIntLiteral of string

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
  | Parser_error of string
  | Lexical_error of Loc.t * string
  | Syntax_error of Loc.t * string
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
  | BitvExtract(i,j) ->
    fprintf fmt "bitvector extraction malformed (%d>%d)" i j
  | BitvExtractRange(n,j) ->
    fprintf fmt "extraction out of range (%d>%d)" j n
  | NonPositiveBitvType(n) ->
    fprintf fmt "non positive bitvector size (%d)" n
  | ClashType s ->
    fprintf fmt "the type %s is already defined" s
  | ClashParam s ->
    fprintf fmt "parameter %s is bound twice" s
  | ClashLabel (s,t) ->
    fprintf fmt "the label %s already appears in type %s" s t
  | CannotGeneralize ->
    fprintf fmt "cannot generalize the type of this expression"
  | TypeDuplicateVar s ->
    fprintf fmt "duplicate type variable %s" s
  | UnboundedVar s ->
    fprintf fmt "unbounded variable %s" s
  | UnknownType s ->
    fprintf fmt "unknown type %s" s
  | WrongArity(s,n) ->
    fprintf fmt "the type %s has %d arguments" s n
  | SymbAlreadyDefined s ->
    fprintf fmt "the symbol %s is already defined" s
  | SymbUndefined s ->
    fprintf fmt "undefined symbol %s" s
  | NotAPropVar s ->
    fprintf fmt "%s is not a propositional variable" s
  | NotAPredicate s ->
    fprintf fmt "%s is not a predicate" s
  | Unification(t1,t2) ->
    fprintf fmt "%a and %a cannot be unified" Ty.print t1 Ty.print t2
  | ShouldBeApply s ->
    fprintf fmt "%s is a function symbol, it should be applied" s
  | WrongNumberofArgs s ->
    fprintf fmt "Wrong number of arguments when applying %s" s
  | ShouldHaveType(ty1,ty2) ->
    fprintf fmt "this expression has type %a but is here used with type %a"
      Ty.print ty1 Ty.print ty2
  | ShouldHaveTypeBitv t ->
    fprintf fmt "this expression has type %a but it should be a bitvector"
      Ty.print t
  | ShouldHaveTypeIntorReal t ->
    fprintf fmt
      "this expression has type %a but it should have type int or real"
      Ty.print t
  | ShouldHaveTypeInt t ->
    fprintf fmt
      "this expression has type %a but it should have type int"
      Ty.print t
  | ShouldHaveTypeArray ->
    fprintf fmt "this expression should have type farray"
  | ShouldHaveTypeRecord t ->
    fprintf fmt "this expression has type %a but it should have a record type"
      Ty.print t
  | ShouldBeARecord ->
    fprintf fmt "this expression should have a record type"
  | ShouldHaveLabel (s, a) ->
    fprintf fmt "this expression has type %s which has no label %s" s a
  | NoLabelInType (lb, ty) ->
    fprintf fmt "no label %s in type %a" (Hstring.view lb) Ty.print ty
  | ShouldHaveTypeProp ->
    fprintf fmt "this expression should have type prop"
  | NoRecordType s ->
    fprintf fmt "no record type has label %s" (Hstring.view s)
  | DuplicateLabel s ->
    fprintf fmt "label %s is defined several times" (Hstring.view s)
  | DuplicatePattern s ->
    fprintf fmt "pattern %s is bound several times" s
  | WrongLabel (s, ty) ->
    fprintf fmt "wrong label %s in type %a" (Hstring.view s) Ty.print ty
  | WrongNumberOfLabels ->
    fprintf fmt "wrong number of labels"
  | ArrayIndexShouldHaveTypeInt ->
    fprintf fmt "index of arrays should hava type int"
  | Notrigger ->
    fprintf fmt "No trigger for this lemma"
  | SyntaxError ->
    fprintf fmt "syntax error"
  | ThExtError s ->
    fprintf fmt "Theory extension %S not recognized" s
  | ThSemTriggerError ->
    fprintf fmt "Semantic triggers are only allowed inside Theories"
  | WrongDeclInTheory ->
    fprintf fmt
      "Currently, this kind of declarations are not allowed inside theories"
  | ShouldBeADT ty ->
    fprintf fmt "%a is not an algebraic, a record or an enumeration datatype"
      Ty.print ty
  | MatchNotExhaustive missing ->
    fprintf fmt
      "Pattern-matching is not exhaustive. These cases are missing: %a"
      (Util.print_list ~sep:" |" ~pp:Hstring.print) missing
  | MatchUnusedCases dead ->
    fprintf fmt
      "Pattern-matching contains unreachable cases. These cases are\
       removed: %a"
      (Util.print_list ~sep:" |" ~pp:Hstring.print) dead
  | NotAdtConstr (lbl, ty) ->
    fprintf fmt
      "The identifiant %s is not a constructor of an algebraic data type. \
       Its type is %a" lbl Ty.print ty
  | BadPopCommand {pushed; to_pop} ->
    fprintf fmt
      "Cannot pop %d assertion contexts. Only %d have been pushed"
      to_pop pushed
  | ShouldBePositive n ->
    fprintf fmt
      "This integer : %d should be positive" n
  | PolymorphicEnum n ->
    fprintf fmt
      "Polymorphic enum definition for %s is not supported" n
  | ShouldBeIntLiteral s ->
    fprintf fmt
      "This expression : %s should be an integer constant" s

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
  | Parser_error s ->
    Format.fprintf fmt "Parser Error: %s" s;
  | Lexical_error (l,s) ->
    Loc.report fmt l;
    Format.fprintf fmt "Lexical Error: %s" s;
  | Syntax_error (l,s) ->
    Loc.report fmt l;
    Format.fprintf fmt "Syntax Error: %s" s;
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
