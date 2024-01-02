(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(* Sat entry *)

type sat_decl_aux =
  | Decl of Id.typed
  | Assume of string * Expr.t * bool
  | PredDef of Expr.t * string (*name of the predicate*)
  | RwtDef of (Expr.t Typed.rwt_rule) list
  | Optimize of Expr.t * bool
  | Query of string *  Expr.t * Ty.goal_sort
  | ThAssume of Expr.th_elt
  | Push of int
  | Pop of int

type sat_tdecl = {
  st_loc : Loc.t;
  st_decl : sat_decl_aux
}

let print_aux fmt = function
  | Decl (id, arg_tys, ret_ty) ->
    Fmt.pf fmt "declare %a with type (%a) -> %a"
      Id.pp id
      Fmt.(list ~sep:comma Ty.print) arg_tys
      Ty.print ret_ty

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
  | Optimize (obj, is_max) ->
    let s = if is_max then "maximize" else "minimize" in
    Format.fprintf fmt "%s %a" s Expr.print obj

let print fmt decl = print_aux fmt decl.st_decl

