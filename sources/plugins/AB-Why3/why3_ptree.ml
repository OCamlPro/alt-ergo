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

(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018 --- OCamlPro SAS                                    *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib

(*s Parse trees. *)

type loc = Loc.t

(*s Logical terms and formulas *)

type integer_constant = string

type constant = string

type label = string

type ident = {
  id_str : string;
  id_lab : label list;
  id_loc : loc;
}

type qualid = Parsed.lexpr

type pty = Parsed.ppure_type

type binder = loc * ident option * Parsed.ppure_type option

type param  = loc * ident option * Parsed.ppure_type

type pattern =
  | Pwild
  | Pvar of ident
  | Ptuple of pattern list
  | Pcast of pattern * pty

type term =  Parsed.lexpr

