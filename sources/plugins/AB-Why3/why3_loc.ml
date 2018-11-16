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
open Lexing


type position = Loc.t

let user_position fname lnum cnum1 cnum2 =
  let upos =
    {pos_fname = fname; pos_lnum = lnum; pos_bol = cnum1;
     pos_cnum = cnum2} in
  (upos, upos)

let get ({pos_fname; pos_lnum; pos_bol; pos_cnum}, _) =
  (pos_fname, pos_lnum, pos_bol, pos_cnum)


let join (p1 : position) (p2 : position) =
  match (get p1, get p2) with
    ((f1, l1, b1, e1), (f2, _, b2, e2 )) ->
    let pos =
      {pos_fname = f1; pos_lnum = l1; pos_bol = b1 ; pos_cnum = e1 + e2 - b2} in
    (pos, pos)

exception Why3_located of position * exn

let error ?loc e = match loc with
  | Some loc -> raise (Why3_located (loc, e))
  | None -> raise e

(* located messages *)

exception Message of string

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
       Format.pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error ?loc (Message s))
    fmt ("@[" ^^ f ^^ "@]")
