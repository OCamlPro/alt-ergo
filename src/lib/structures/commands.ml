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

(* Sat entry *)

let src = Logs.Src.create ~doc:"Commands" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

type sat_decl_aux =
  | Decl of Symbols.typed_name
  | Assume of string * Expr.t * bool
  | PredDef of Expr.t * string (*name of the predicate*)
  | RwtDef of (Expr.t Typed.rwt_rule) list
  | Optimize of Objective.Function.t
  | Query of string *  Expr.t * Ty.goal_sort
  | ThAssume of Expr.th_elt
  | Push of int
  | Pop of int

type sat_tdecl = {
  st_loc : Loc.t;
  st_decl : sat_decl_aux
}

let print_aux fmt = function
  | Decl tn ->
    Fmt.pf fmt "declare %a" Symbols.pp_typed_name tn

  | Assume (name, e, b) ->
    Format.fprintf fmt "assume %s(%b): @[<hov>%a@]" name b Expr.print e
  | PredDef (e, name) ->
    Format.fprintf fmt "pred-def %s: @[<hov>%a@]" name Expr.print e
  | RwtDef l ->
    Format.fprintf fmt "rwrts: @[<v>%a@]"
      (Util.print_list_pp
         ~sep:Format.pp_print_space
         ~pp:(Typed.print_rwt Expr.print)
      ) l
  | Query (name, e, sort) ->
    Format.fprintf fmt "query %s(%a): @[<hov>%a@]"
      name Ty.print_goal_sort sort Expr.print e
  | ThAssume t ->
    Format.fprintf fmt "th assume %a" Expr.print_th_elt t
  | Push n -> Format.fprintf fmt "Push %d" n
  | Pop n ->  Format.fprintf fmt "Pop %d" n
  | Optimize { e; is_max; _ }  ->
    let s = if is_max then "maximize" else "minimize" in
    Format.fprintf fmt "%s %a" s Expr.print e

let print fmt decl = print_aux fmt decl.st_decl

