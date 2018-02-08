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

(** Useful option combinators *)
(*
val inhabited : 'a option -> bool

val get : 'a option -> 'a

val get_exn : exn -> 'a option -> 'a

val get_def : 'a -> 'a option -> 'a
 *)
val map : ('a -> 'b) -> 'a option -> 'b option
 
val iter : ('a -> unit) -> 'a option -> unit
(*
val apply : 'b -> ('a -> 'b) option -> 'a -> 'b

val apply2 : 'c -> ('a -> 'b -> 'c) option -> 'a -> 'b -> 'c

val fold : ('b -> 'a -> 'b) -> 'b -> 'a option -> 'b
(** [fold f d o] returns [d] if [o] is [None], and
    [f d x] if [o] is [Some x] *)

val fold_right : ('a -> 'b -> 'b) -> 'a option -> 'b -> 'b

val map2 : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option

val equal : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool

val compare : ('a -> 'b -> int) -> 'a option -> 'b option -> int

val map_fold : ('a -> 'b -> 'a * 'b) -> 'a -> 'b option -> 'a * 'b option*)
