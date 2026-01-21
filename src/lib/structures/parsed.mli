(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

type constant =
  | ConstBitv of string
  | ConstInt of string
  | ConstReal of Num.num
  | ConstTrue
  | ConstFalse
  | ConstVoid

type pp_infix =
  | PPand | PPor | PPxor | PPimplies | PPiff
  | PPlt | PPle | PPgt | PPge | PPeq | PPneq
  | PPadd | PPsub | PPmul | PPdiv | PPmod
  | PPpow_int | PPpow_real

type pp_prefix =
  | PPneg | PPnot

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTbitv of int
  | PPTvarid of string * Loc.t
  | PPTexternal of ppure_type list * string * Loc.t

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
  | Logic of Loc.t * Symbols.name_kind * (string * string) list * plogic_type
  | Predicate_def of
      Loc.t * (string * string) *
      (Loc.t * string * ppure_type) list * lexpr
  | Function_def of
      Loc.t * (string * string) *
      (Loc.t * string * ppure_type) list * ppure_type * lexpr
  | TypeDecl of type_decl list
  | Push of Loc.t * int
  | Pop of Loc.t * int

type file = decl list
