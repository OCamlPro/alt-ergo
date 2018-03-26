(*******************************************************************************)
(*                                                                             *)
(*   W34AE: A parser of Why3 logic for Alt-Ergo                                *)
(*                                                                             *)
(*   Copyright 2011-2017 OCamlPro SAS                                          *)
(*                                                                             *)
(*   All rights reserved.  This file is distributed under the terms of         *)
(*   the GNU Lesser General Public License version 2.1, with the               *)
(*   special exception on linking described in the file LICENSE.               *)
(*                                                                             *)
(*******************************************************************************)


type loc = Loc.t
type integer_constant = string
type constant = string
type label  = string



type ident = { id_str : string; id_lab : label list; id_loc : loc; }
type qualid = Parsed.lexpr
type pty = Parsed.ppure_type

type binder = loc * ident option * Parsed.ppure_type option
type param = loc * ident option * Parsed.ppure_type
type pattern =
  | Pwild
  | Pvar of ident
  | Ptuple of pattern list
  | Pcast of pattern * pty
type term =  Parsed.lexpr
