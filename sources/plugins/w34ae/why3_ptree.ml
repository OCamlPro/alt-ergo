(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*s Parse trees. *)
open Big_int

type ind_sign = Ind | Coind

type prop_kind =
  | Plemma    
  | Paxiom    
  | Pgoal     
  | Pskip 

type loc = Why3_loc.position

(*s Logical terms and formulas *)

type integer_constant = Why3_number.integer_constant
type real_constant = Why3_number.real_constant
type constant = Why3_number.constant

type w3idlabel = { lab_string : string }

type label =
  | Lstr of w3idlabel
  | Lpos of Why3_loc.position

type quant =
  | Tforall | Texists | Tlambda

type binop =
  | Tand | Tand_asym | Tor | Tor_asym | Timplies | Tiff | Tby | Tso

type unop =
  | Tnot

type ident = {
  id_str : string;
  id_lab : label list;
  id_loc : loc;
}

type qualid =
  | Qident of ident
  | Qdot of qualid * ident

type pty = Parsed.ppure_type

type ghost = bool

type binder = loc * ident option * Parsed.ppure_type option
type param  = loc * ident option * Parsed.ppure_type

type pattern = {
  pat_desc : pat_desc;
  pat_loc  : loc;
}

and pat_desc =
  | Pwild
  | Pvar of ident
  | Papp of qualid * pattern list
  | Prec of (qualid * pattern) list
  | Ptuple of pattern list
  | Por of pattern * pattern
  | Pas of pattern * ident
  | Pcast of pattern * pty

type term =  Parsed.lexpr
               

(*s Why3_declarations. *)

type use = {
  use_theory : qualid;
  use_import : (bool (* import *) * string (* as *)) option;
}

type clone_subst =
  | CSns    of loc * qualid option * qualid option
  | CStsym  of loc * qualid * ident list * pty
  | CSfsym  of loc * qualid * qualid
  | CSpsym  of loc * qualid * qualid
  | CSvsym  of loc * qualid * qualid
  | CSlemma of loc * qualid
  | CSgoal  of loc * qualid


type type_def =
  | TDabstract
  | TDalias     of pty
  | TDalgebraic of (loc * ident * param list) list
  | TDrange     of big_int * big_int
  | TDfloat     of int * int

type visibility = Public | Private | Abstract

type invariant = term list

type type_decl = {
  td_loc    : loc;
  td_ident  : ident;
  td_params : ident list;
  td_model  : bool;
  td_vis    : visibility;
  td_def    : type_def;
  td_inv    : invariant;
}

type logic_decl = {
  ld_loc    : loc;
  ld_ident  : ident;
  ld_params : param list;
  ld_type   : pty option;
  ld_def    : term option;
}

type use_clone = use * clone_subst list option

type decl =
  | Dtype of type_decl list
  | Dlogic of logic_decl list
  | Dprop of prop_kind * ident * term
