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

type loc = Loc.t

(*s Logical terms and formulas *)

type integer_constant = string
                          
type constant = string

type w3idlabel = { lab_string : string }

type label =
  | Lstr of w3idlabel
  | Lpos of Loc.t

type ident = {
  id_str : string;
  id_lab : label list;
  id_loc : loc;
}

type qualid = Parsed.lexpr

type pty = Parsed.ppure_type

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

type invariant = term list                     

type use_clone = use * clone_subst list option
