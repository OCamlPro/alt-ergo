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

module In_channel = struct
  open In_channel

  (* Best effort attempt to return a buffer with >= (ofs + n) bytes of storage,
     and such that it coincides with [buf] at indices < [ofs].
     The returned buffer is equal to [buf] itself if it already has sufficient
     free space.
     The returned buffer may have *fewer* than [ofs + n] bytes of storage if this
     number is > [Sys.max_string_length]. However the returned buffer will
     *always* have > [ofs] bytes of storage. In the limiting case when [ofs = len
     = Sys.max_string_length] (so that it is not possible to resize the buffer at
     all), an exception is raised. *)

  let ensure buf ofs n =
    let len = Bytes.length buf in
    if len >= ofs + n then buf
    else begin
      let new_len = ref len in
      while !new_len < ofs + n do
        new_len := 2 * !new_len + 1
      done;
      let new_len = !new_len in
      let new_len =
        if new_len <= Sys.max_string_length then
          new_len
        else if ofs < Sys.max_string_length then
          Sys.max_string_length
        else
          failwith "In_channel.input_all: channel content \
                    is larger than maximum string length"
      in
      let new_buf = Bytes.create new_len in
      Bytes.blit buf 0 new_buf 0 ofs;
      new_buf
    end

  (* Read up to [len] bytes into [buf], starting at [ofs]. Return total bytes
     read. *)
  let read_upto ic buf ofs len =
    let rec loop ofs len =
      if len = 0 then ofs
      else begin
        let r = Stdlib.input ic buf ofs len in
        if r = 0 then
          ofs
        else
          loop (ofs + r) (len - r)
      end
    in
    loop ofs len - ofs

  let input_all ic =
    let chunk_size = 65536 in (* IO_BUFFER_SIZE *)
    let initial_size =
      try
        Stdlib.in_channel_length ic - Stdlib.pos_in ic
      with Sys_error _ ->
        -1
    in
    let initial_size = if initial_size < 0 then chunk_size else initial_size in
    let initial_size =
      if initial_size <= Sys.max_string_length then
        initial_size
      else
        Sys.max_string_length
    in
    let buf = Bytes.create initial_size in
    let nread = read_upto ic buf 0 initial_size in
    if nread < initial_size then (* EOF reached, buffer partially filled *)
      Bytes.sub_string buf 0 nread
    else begin (* nread = initial_size, maybe EOF reached *)
      match Stdlib.input_char ic with
      | exception End_of_file ->
        (* EOF reached, buffer is completely filled *)
        Bytes.unsafe_to_string buf
      | c ->
        (* EOF not reached *)
        let rec loop buf ofs =
          let buf = ensure buf ofs chunk_size in
          let rem = Bytes.length buf - ofs in
          (* [rem] can be < [chunk_size] if buffer size close to
             [Sys.max_string_length] *)
          let r = read_upto ic buf ofs rem in
          if r < rem then (* EOF reached *)
            Bytes.sub_string buf 0 (ofs + r)
          else (* r = rem *)
            loop buf (ofs + rem)
        in
        let buf = ensure buf nread (chunk_size + 1) in
        Bytes.set buf nread c;
        loop buf (nread + 1)
    end

  include In_channel
end
