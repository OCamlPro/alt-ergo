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

(* locations in files *)

type position = Loc.t

val join : position -> position -> position

val dummy_position : position

val user_position : string -> int -> int -> int -> position

val get : position -> string * int * int * int

(* located exceptions *)

exception Why3_located of position * exn

val error: ?loc:position -> exn -> 'a

(* messages *)

exception Message of string
 
val errorm: ?loc:position -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val with_location: (Lexing.lexbuf -> 'a) -> (Lexing.lexbuf -> 'a)
