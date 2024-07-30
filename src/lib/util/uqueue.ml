(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module type S = sig
  type elt

  type t

  val create : int -> t

  val push : t -> elt -> unit

  exception Empty

  val pop : t -> elt

  val peek : t -> elt

  val is_empty : t -> bool

  val clear : t -> unit
end

module Make(H : Hashtbl.HashedType) : S with type elt = H.t = struct
  module HT = Hashtbl.Make(H)

  type elt = H.t

  type t = { queue : H.t Queue.t ; elements : unit HT.t}

  let create n =
    { queue = Queue.create () ; elements = HT.create n }

  let push { queue ; elements } x =
    if HT.mem elements x then () else (
      HT.replace elements x ();
      Queue.push x queue
    )

  exception Empty = Queue.Empty

  let pop { queue ; elements } =
    let x = Queue.pop queue in
    HT.remove elements x; x

  let peek { queue; _ } = Queue.peek queue

  let is_empty { queue; _ } = Queue.is_empty queue

  let clear { queue ; elements } =
    Queue.clear queue; HT.clear elements
end
