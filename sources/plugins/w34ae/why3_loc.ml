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

(*
type lexing_loc = Lexing.position * Lexing.position
*)

open Lexing
(*
let current_offset = ref 0
let reloc p = { p with pos_cnum = p.pos_cnum + !current_offset }

let set_file file lb =
  lb.Lexing.lex_curr_p <-
    { lb.Lexing.lex_curr_p with Lexing.pos_fname = file }

let transfer_loc lb_from lb_to =
  lb_to.lex_start_p <- lb_from.lex_start_p;
  lb_to.lex_curr_p <- lb_from.lex_curr_p
 *)

(*s Error locations. *)

(* dead code
let finally ff f x =
  let y = try f x with e -> ff (); raise e in ff (); y
*)

(*open Format*)

(*s Line number *)

(*
let report_line fmt l = fprintf fmt "%s:%d:" l.pos_fname l.pos_lnum
*)

type position = string * int * int * int

let user_position fname lnum cnum1 cnum2 = (fname,lnum,cnum1,cnum2)

let get loc = loc

let dummy_position = ("",0,0,0)
 
let join (f1,l1,b1,e1) (f2,_,b2,e2) =
  assert (f1 = f2); (f1,l1,b1,e1+e2-b2)
 
let extract (b,e) =
  let f = b.pos_fname in
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol in
  let lc = e.pos_cnum - b.pos_bol in
  (f,l,fc,lc)
(*
let compare = Pervasives.compare
let equal = Pervasives.(=)
let hash = Hashtbl.hash

let gen_report_position fmt (f,l,b,e) =
  fprintf fmt "File \"%s\", line %d, characters %d-%d" f l b e

let report_position fmt = fprintf fmt "%a:@\n" gen_report_position
*)
(* located exceptions *)

exception Why3_located of position * exn
 
let error ?loc e = match loc with
  | Some loc -> raise (Why3_located (loc, e))
  | None -> raise e
(*
let try1 ?loc f x =
  if Debug.test_flag Debug.stack_trace then f x else
  try f x with Why3_located _ as e -> raise e | e -> error ?loc e

let try2 ?loc f x y =
  if Debug.test_flag Debug.stack_trace then f x y else
  try f x y with Why3_located _ as e -> raise e | e -> error ?loc e

let try3 ?loc f x y z =
  if Debug.test_flag Debug.stack_trace then f x y z else
  try f x y z with Why3_located _ as e -> raise e | e -> error ?loc e

let try4 ?loc f x y z t =
  if Debug.test_flag Debug.stack_trace then f x y z t else
  try f x y z t with Why3_located _ as e -> raise e | e -> error ?loc e

let try5 ?loc f x y z t u =
  if Debug.test_flag Debug.stack_trace then f x y z t u else
  try f x y z t u with Why3_located _ as e -> raise e | e -> error ?loc e

let try6 ?loc f x y z t u v =
  if Debug.test_flag Debug.stack_trace then f x y z t u v else
  try f x y z t u v with Why3_located _ as e -> raise e | e -> error ?loc e

let try7 ?loc f x y z t u v w =
  if Debug.test_flag Debug.stack_trace then f x y z t u v w else
  try f x y z t u v w with Why3_located _ as e -> raise e | e -> error ?loc e

(* located messages *)
 *)
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
(*
let () = Why3_exn_printer.register
  (fun fmt exn -> match exn with
    | Why3_located (loc,e) ->
        fprintf fmt "%a%a" report_position loc Why3_exn_printer.exn_printer e
    | Message s ->
        fprintf fmt "%s" s
    | _ ->
        raise exn)
 *)
let loc lb = extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)
(*
let with_location f lb =
  if Debug.test_flag Debug.stack_trace then f lb else
    try f lb with
    | Why3_located _ as e -> raise e
    | e -> raise (Why3_located (loc lb, e))*)

let with_location f lb =
  (*if Debug.test_flag Debug.stack_trace then f lb else*)
    try f lb with
    | Why3_located _ as e -> raise e
    | e -> raise (Why3_located (loc lb, e))
