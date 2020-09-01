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

[@@@ocaml.warning "-33"]
open Options

type constant =
  | ConstBitv of string
  | ConstInt of string
  | ConstReal of Num.num
  | ConstTrue
  | ConstFalse
  | ConstVoid

let pp_const fmt =
  let open Format in
  function
  | ConstBitv s -> fprintf fmt "%s" s
  | ConstInt s -> fprintf fmt "%s" s
  | ConstReal v -> fprintf fmt "%s" (Num.string_of_num v)
  | ConstTrue -> fprintf fmt "true"
  | ConstFalse -> fprintf fmt "false"
  | ConstVoid -> fprintf fmt "void"

type pp_infix =
  | PPand | PPor | PPxor | PPimplies | PPiff
  | PPlt | PPle | PPgt | PPge | PPeq | PPneq
  | PPadd | PPsub | PPmul | PPdiv | PPmod
  | PPpow_int | PPpow_real

let pp_inf_op fmt =
  let open Format in
  function
  | PPand -> fprintf fmt "and"
  | PPor -> fprintf fmt "or"
  | PPxor -> fprintf fmt "xor"
  | PPimplies -> fprintf fmt "implies"
  | PPiff -> fprintf fmt "iff"
  | PPlt -> fprintf fmt "lt"
  | PPle -> fprintf fmt "le"
  | PPgt -> fprintf fmt "gt"
  | PPge -> fprintf fmt "ge"
  | PPeq -> fprintf fmt "eq"
  | PPneq -> fprintf fmt "neq"
  | PPadd -> fprintf fmt "add"
  | PPsub -> fprintf fmt "sub"
  | PPmul -> fprintf fmt "mul"
  | PPdiv -> fprintf fmt "div"
  | PPmod -> fprintf fmt "mod"
  | PPpow_int -> fprintf fmt "pow_int"
  | PPpow_real -> fprintf fmt "pow_real"

type pp_prefix =
  | PPneg | PPnot

let pp_pre_op fmt =
  let open Format in
  function
  | PPneg -> fprintf fmt "-"
  | PPnot -> fprintf fmt "not"

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTbitv of int
  | PPTvarid of string * Loc.t
  | PPTexternal of ppure_type list * string * Loc.t

let pp_sep_comma fmt () = Format.fprintf fmt ","

let pp_sep_space fmt () = Format.fprintf fmt " "

let rec pp_ppure_type fmt t =
  Format.fprintf fmt "%s"
    (match t with
     | PPTint -> "int"
     | PPTbool -> "bool"
     | PPTreal -> "real"
     | PPTunit -> "unit"
     | PPTbitv i -> Format.asprintf "bitv[%d]" i
     | PPTvarid (s, _) -> Format.asprintf "varid[%s]" s
     | PPTexternal (ppl, s, _) ->
       Format.asprintf "%a %s" pp_ppure_type_list ppl s
    )

and pp_ppure_type_list fmt tl =
  Format.fprintf fmt "@[<h>%a@]"
    (Format.pp_print_list ~pp_sep:pp_sep_comma (fun fmt t ->
         Format.fprintf fmt "%a" pp_ppure_type t)) tl

and pp_str_ppure_type_list fmt tl =
  Format.fprintf fmt "@[<h>%a@]"
    (Format.pp_print_list ~pp_sep:pp_sep_comma (fun fmt (s, t) ->
         Format.fprintf fmt "(%s, %a)" s pp_ppure_type t)) tl

and pp_str_str_ppure_type_list fmt tl =
  Format.fprintf fmt "@[<h>%a@]"
    (Format.pp_print_list ~pp_sep:pp_sep_comma (fun fmt (s1, s2, t) ->
         Format.fprintf fmt "(%s, %s, %a)" s1 s2 pp_ppure_type t)) tl

type pattern =
  { pat_loc : Loc.t; pat_desc : string * string list }

type lexpr =
  { pp_loc : Loc.t; pp_desc : pp_desc }

and pp_desc =
  | PPvar of string
  | PPapp of string * lexpr list
  | PPmapsTo of string * lexpr
  | PPinInterval of lexpr * bool * lexpr * lexpr * bool
  (* bool = true <-> interval is_open *)

  | PPdistinct of lexpr list
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPget of lexpr * lexpr
  | PPset of lexpr * lexpr * lexpr
  | PPdot of lexpr * string
  | PPrecord of (string * lexpr) list
  | PPwith of lexpr * (string * lexpr) list
  | PPextract of lexpr * lexpr * lexpr
  | PPconcat of lexpr * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of
      (string * ppure_type) list * (lexpr list * bool) list * lexpr list * lexpr
  | PPexists of
      (string * ppure_type) list * (lexpr list * bool) list * lexpr list * lexpr
  | PPforall_named of
      (string * string * ppure_type) list * (lexpr list * bool) list *
      lexpr list * lexpr
  | PPexists_named of
      (string * string * ppure_type) list * (lexpr list * bool) list *
      lexpr list * lexpr
  | PPnamed of string * lexpr
  | PPlet of (string * lexpr) list * lexpr
  | PPcheck of lexpr
  | PPcut of lexpr
  | PPcast of lexpr * ppure_type
  | PPmatch of lexpr * (pattern * lexpr) list
  | PPisConstr of lexpr * string
  | PPproject of bool * lexpr * string

let rec pp_lexpr fmt {pp_desc; _} =
  let open Format in
  match pp_desc with
  | PPvar s ->
    fprintf fmt "%s" s
  | PPapp (s, lel) ->
    fprintf fmt "PPapp(%s, %a)" s (pp_print_list ~pp_sep:pp_sep_space pp_lexpr) lel
  | PPmapsTo (s, le) ->
    fprintf fmt "[%s -> %a]" s pp_lexpr le
  | PPinInterval (le, b1, le1, le2, b2) ->
    fprintf fmt "%a in %c %a, %a %c"
      pp_lexpr le
      (if b1 then ']' else '[')
      pp_lexpr le1
      pp_lexpr le2
      (if b2 then ']' else '[')
  | PPdistinct lel ->
    fprintf fmt "distincts (%a)" (pp_print_list pp_lexpr) lel
  | PPconst c->
    fprintf fmt "%a" pp_const c
  | PPinfix (le1, op, le2) ->
    fprintf fmt "inf: (%a %a %a)" pp_lexpr le1 pp_inf_op op pp_lexpr le2
  | PPprefix (op, le) ->
    fprintf fmt "pre: %a %a" pp_pre_op op pp_lexpr le
  | PPget (arr, ind) ->
    fprintf fmt "%a[%a]" pp_lexpr arr pp_lexpr ind
  | PPset (arr, ind, v) ->
    fprintf fmt "%a[%a] <- %a" pp_lexpr arr pp_lexpr ind pp_lexpr v
  | PPdot (le, s) ->
    fprintf fmt "%a.%s" pp_lexpr le s
  | PPrecord l ->
    fprintf fmt "{%a}"
      (pp_print_list (fun fmt (s, le) -> fprintf fmt "%s = %a" s pp_lexpr le)) l
  | PPwith (le, l) ->
    fprintf fmt "{%a with %a}" pp_lexpr le
      (pp_print_list (fun fmt (s, le) -> fprintf fmt "%s = %a" s pp_lexpr le)) l
  | PPextract (le1, le2, le3) ->
    fprintf fmt "Extract (%a, %a, %a)" pp_lexpr le1 pp_lexpr le2 pp_lexpr le3
  | PPconcat (le1, le2) ->
    fprintf fmt "%a^%a" pp_lexpr le1 pp_lexpr le2
  | PPif (cond, bthen, belse) ->
    fprintf fmt "if %a then %a else %a"
      pp_lexpr cond pp_lexpr bthen pp_lexpr belse
  (* Used for an experiment so not complete but will be completed *)
  | PPforall (spptl, lebl, lel, le) ->
    fprintf fmt "forall %a. [%a] [%a] %a"
      pp_str_ppure_type_list spptl pp_lexprl_bool_list lebl
      pp_lexpr_list lel pp_lexpr le
  | PPexists (_spptl, _lebl, _lel, _le) -> fprintf fmt "exists"
  | PPforall_named (sspptl, lebl, lel, le) ->
    fprintf fmt "foralln %a. [%a] [%a] %a"
      pp_str_str_ppure_type_list sspptl pp_lexprl_bool_list lebl
      pp_lexpr_list lel pp_lexpr le
  | PPexists_named (_spptl, _lebl, _lel, _le) -> fprintf fmt "existsn"
  | PPnamed (s, le) -> fprintf fmt "Named: %s %a" s pp_lexpr le
  | PPlet (_slel, _le) -> fprintf fmt "let"
  | PPcheck le -> fprintf fmt "check %a" pp_lexpr le
  | PPcut le -> fprintf fmt "cut %a" pp_lexpr le
  | PPcast (le, ppt) -> fprintf fmt "cast %a -> %a" pp_lexpr le pp_ppure_type ppt
  | PPmatch (_le, _plel) -> fprintf fmt "match"
  | PPisConstr (le, s) -> fprintf fmt "isConstr: %a %s" pp_lexpr le s
  | PPproject (b, le, s) -> fprintf fmt "project: %b %a %s" b pp_lexpr le s

and pp_lexpr_list fmt tl =
  Format.fprintf fmt "@[<h>%a@]"
    (Format.pp_print_list ~pp_sep:pp_sep_comma (fun fmt e ->
         Format.fprintf fmt "%a" pp_lexpr e)) tl

and pp_lexprl_bool_list fmt tl =
  Format.fprintf fmt "@[<h>%a@]"
    (Format.pp_print_list ~pp_sep:pp_sep_comma (fun fmt (lel, b) ->
         Format.fprintf fmt "(%a, %b)" pp_lexpr_list lel b)) tl

(* Declarations. *)

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type body_type_decl =
  | Record of string * (string * ppure_type) list  (* lbl : t *)
  | Enum of string list
  | Algebraic of (string * (string * ppure_type) list) list
  | Abstract

type type_decl = Loc.t * string list * string * body_type_decl

type decl =
  | Theory of Loc.t * string * string * decl list
  | Axiom of Loc.t * string * Util.axiom_kind * lexpr
  | Rewriting of Loc.t * string * lexpr list
  | Goal of Loc.t * string * lexpr
  | Check_sat of Loc.t * string * lexpr
  | Logic of Loc.t * Symbols.name_kind * (string * string) list * plogic_type
  | Predicate_def of
      Loc.t * (string * string) *
      (Loc.t * string * ppure_type) list * lexpr
  | Function_def of
      Loc.t * (string * string) *
      (Loc.t * string * ppure_type) list * ppure_type * lexpr
  | TypeDecl of type_decl list

type file = decl list
