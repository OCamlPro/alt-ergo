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

(** {1 Errors module} *)

(** This module aims to regroup all exception that can be raised
    by the Alt-Ergo-lib *)

(** {2 Error types } *)

(** Error that can be raised by the typechecker *)
type typing_error =
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
  | BadPopCommand of {pushed : int; to_pop : int}
  | ShouldBePositive of int
  | ShouldBeIntLiteral of string

(** Errors that can be raised at solving*)
type run_error =
  | Invalid_steps_count of int
  | Steps_limit of int
  | Failed_check_unsat_core
  | Unsupported_feature of string
  | Dynlink_error of string

(** All types of error that can be raised *)
type error =
  | Parser_error of string (** Error used at parser loading *)
  | Lexical_error of Loc.t * string (** Error used by the lexer *)
  | Syntax_error of Loc.t * string (** Error used by the parser*)
  | Typing_error of Loc.t * typing_error (** Error used at typing *)
  | Run_error of run_error (** Error used during solving *)
  | Warning_as_error

(** {2 Exceptions } *)

exception Error of error

(** {3 Raising exceptions functions } *)

(** Raise the input error as {!Error} *)
val error : error -> 'a

(** Raise the input {!typing_error} as {!Typing_error} *)
val typing_error : typing_error -> Loc.t -> 'a

(** Raise the input {!run_error} as {!Run_error} *)
val run_error : run_error -> 'a

(** Raise [Warning_as_error] as {!Error}
    if the option warning-as-error is set
    This function can be use after warning *)
val warning_as_error : unit -> unit

(** {2 Printing } *)

(** Print a message on the formatter corresponding to the error *)
val report : Format.formatter -> error -> unit
