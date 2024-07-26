(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "-32-33"]

module List = struct
  open List

  let is_empty = function
    | [] -> true
    | _ -> false

  let rec equal eq l1 l2 =
    match l1, l2 with
    | [], [] -> true
    | [], _::_ | _::_, [] -> false
    | a1::l1, a2::l2 -> eq a1 a2 && equal eq l1 l2

  let rec compare cmp l1 l2 =
    match l1, l2 with
    | [], [] -> 0
    | [], _::_ -> -1
    | _::_, [] -> 1
    | a1::l1, a2::l2 ->
      let c = cmp a1 a2 in
      if c <> 0 then c
      else compare cmp l1 l2

  let rec find_map f = function
    | [] -> None
    | x :: l ->
      begin match f x with
        | Some _ as result -> result
        | None -> find_map f l
      end

  let fold_left_map f accu l =
    let rec aux accu l_accu = function
      | [] -> accu, rev l_accu
      | x :: l ->
        let accu, x = f accu x in
        aux accu (x :: l_accu) l in
    aux accu [] l

  include List
end

module Bytes = struct
  open Bytes

  let fold_left f x a =
    let r = ref x in
    for i = 0 to length a - 1 do
      r := f !r (unsafe_get a i)
    done;
    !r

  include Bytes
end

module String = struct
  open String

  let fold_left f a x =
    Bytes.fold_left f a (Bytes.unsafe_of_string x)

  let starts_with ~prefix s =
    let len_s = length s
    and len_pre = length prefix in
    let rec aux i =
      if i = len_pre then true
      else if not @@ Char.equal (unsafe_get s i) (unsafe_get prefix i) then
        false
      else aux (i + 1)
    in len_s >= len_pre && aux 0

  include String
end

module Seq = struct
  open Seq

  let uncons xs =
    match xs() with
    | Cons (x, xs) ->
      Some (x, xs)
    | Nil ->
      None

  let is_empty xs =
    match xs() with
    | Nil ->
      true
    | Cons (_, _) ->
      false

  let rec append seq1 seq2 () =
    match seq1() with
    | Nil -> seq2()
    | Cons (x, next) -> Cons (x, append next seq2)

  let rec equal eq xs ys =
    match xs(), ys() with
    | Nil, Nil ->
      true
    | Cons (x, xs), Cons (y, ys) ->
      eq x y && equal eq xs ys
    | Nil, Cons (_, _)
    | Cons (_, _), Nil ->
      false

  include Seq
end

module Type = struct
  type (_, _) eq = Equal : ('a, 'a) eq

  module Id = struct
    type _ id = ..

    module type ID = sig
      type t
      type _ id += Id : t id
    end

    type 'a t = (module ID with type t = 'a)

    let make (type a) () : a t =
      (module struct type t = a type _ id += Id : t id end)

    let[@inline] uid (type a) ((module A) : a t) =
      Obj.Extension_constructor.id (Obj.Extension_constructor.of_val A.Id)

    let provably_equal
        (type a b) ((module A) : a t) ((module B) : b t) : (a, b) eq option
      =
      match A.Id with B.Id -> Some Equal | _ -> None
  end
end
