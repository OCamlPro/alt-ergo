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

(*s Hash tables for hash-consing. (Some code is borrowed from the ocaml
    standard library, which is copyright 1996 INRIA.) *)

module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val tag : int -> t -> t
  end

module type S =
  sig
    type t
    val hashcons : t -> t
    val unique : t -> t
    val iter : (t -> unit) -> unit
    val stats : unit -> int * int * int * int * int * int
  end

module Make(H : HashedType) : (S with type t = H.t) =
struct
  type t = H.t

  module WH = Weak.Make (H)

  let next_tag = ref 0

  let htable = WH.create 5003

  let hashcons d =
    let d = H.tag !next_tag d in
    let o = WH.merge htable d in
    if o == d then incr next_tag;
    o

  let unique d =
    let d = H.tag !next_tag d in
    incr next_tag;
    d

  let iter f = WH.iter f htable

  let stats () = WH.stats htable
end

let combine acc n = acc * 65599 + n
let combine2 acc n1 n2 = combine (combine acc n1) n2
let combine3 acc n1 n2 n3 = combine (combine2 acc n1 n2) n3
let combine_list f acc l = List.fold_left (fun acc x -> combine acc (f x)) acc l
let combine_option h = function None -> -1 | Some s -> h s
let combine_pair h1 h2 (a1,a2) = combine (h1 a1) (h2 a2)
