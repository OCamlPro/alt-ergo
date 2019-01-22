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

open Format

type error =
  | BitvExtract of int*int
  | BitvExtractRange of int*int
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

(* this is a typing error *)
exception Error of error * Loc.t

(* these two exception are used by the lexer and the parser *)
exception Lexical_error of Loc.t * string
exception Syntax_error of Loc.t * string


let report fmt = function
  | BitvExtract(i,j) ->
    fprintf fmt "bitvector extraction malformed (%d>%d)" i j
  | BitvExtractRange(n,j) ->
    fprintf fmt "extraction out of range (%d>%d)" j n
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
    fprintf fmt "%s is a function symbol, it should be apply" s
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
      "Pattern-matching contains unreachable cases. These cases are removed: %a"
      (Util.print_list ~sep:" |" ~pp:Hstring.print) dead

  | NotAdtConstr (lbl, ty) ->
    fprintf fmt
      "The symbol %s is not a constructor of the type %a" lbl Ty.print ty

let error e l = raise (Error(e,l))
let warning e l =
  if Options.unsat_mode () then Format.fprintf err_formatter "; ";
  Loc.report err_formatter l;
  report err_formatter e;
  Format.eprintf "@."
