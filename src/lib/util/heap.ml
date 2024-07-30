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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module type RankedType = sig
  type t

  val index : t -> int

  val set_index : t -> int -> unit

  val compare : t -> t -> int
end

module MakeRanked(Rank : RankedType) = struct
  type elt = Rank.t

  type t = { heap : elt Vec.t } [@@unboxed]

  (* Negative value; used to indicate an element is not in the heap *)
  let absent = -1

  let create sz dummy = { heap = Vec.make ~dummy sz }

  let[@inline] left i = (i lsl 1) + 1 (* i*2 + 1 *)
  let[@inline] right i = (i + 1) lsl 1 (* (i + 1) * 2*)
  let[@inline] parent i = (i - 1) asr 1 (* (i - 1) / 2 *)

  let percolate_up { heap } x =
    let pi = ref (parent (Rank.index x)) in
    let i = ref (Rank.index x) in
    while !i <> 0 && Rank.compare x (Vec.get heap !pi) < 0 do
      Vec.set heap !i (Vec.get heap !pi);
      Rank.set_index (Vec.get heap !i) !i;
      i  := !pi;
      pi := parent !i
    done;
    Vec.set heap !i x;
    Rank.set_index x !i

  let percolate_down { heap } x =
    let sz = Vec.size heap in
    let li = ref (left (Rank.index x)) in
    let ri = ref (right (Rank.index x)) in
    let i = ref (Rank.index x) in
    (try
       while !li < sz do
         let child =
           if !ri < sz && Rank.compare (Vec.get heap !ri) (Vec.get heap !li) < 0
           then !ri
           else !li
         in
         if not (Rank.compare (Vec.get heap child) x < 0) then raise Exit;
         Vec.set heap !i (Vec.get heap child);
         Rank.set_index (Vec.get heap !i) !i;
         i  := child;
         li := left !i;
         ri := right !i
       done;
     with Exit -> ());
    Vec.set heap !i x;
    Rank.set_index x !i

  let[@inline] in_heap x = Rank.index x >= 0

  let[@inline] decrease s x = assert (in_heap x); percolate_up s x

  let[@inline] increase s x = assert (in_heap x); percolate_down s x

  let filter ({ heap } as s) filt =
    let j = ref 0 in
    let lim = Vec.size heap in
    for i = 0 to lim - 1 do
      let elt = Vec.get heap i in
      if filt elt then begin
        Vec.set heap !j elt;
        Rank.set_index elt !j;
        incr j;
      end
      else Rank.set_index elt absent;
    done;
    Vec.shrink heap !j;
    for i = (lim / 2) - 1 downto 0 do
      percolate_down s (Vec.get heap i)
    done

  let[@inline] size s = Vec.size s.heap

  let[@inline] is_empty s = Vec.is_empty s.heap

  let insert s x =
    if not (in_heap x) then
      begin
        Rank.set_index x (Vec.size s.heap);
        Vec.push s.heap x;
        percolate_up s x
      end

  let[@inline] grow_to_by_double { heap } sz =
    Vec.grow_to_by_double heap sz

  let pop_min ({ heap } as s) =
    match Vec.size heap with
    | 0 -> raise Not_found
    | 1 ->
      let x = Vec.pop heap in
      Rank.set_index x absent;
      x
    | _ ->
      let x = Vec.get heap 0 in
      let y = Vec.pop s.heap in
      Vec.set heap 0 y;
      Rank.set_index y 0;
      Rank.set_index x absent;
      (* enforce heap invariants *)
      if Vec.size s.heap > 1 then percolate_down s y;
      x
end

module type OrderedTypeDefault = sig
  type t

  val compare : t -> t -> int

  val default : t
end

module MakeOrdered(V : OrderedTypeDefault) = struct
  type entry = { value : V.t ; mutable index : int }
  type elt = V.t

  module H = MakeRanked
      (struct
        type t = entry

        let index e = e.index

        let set_index e i = e.index <- i

        let compare x y = V.compare x.value y.value
      end)

  let entry value = { value ; index = -1 }

  type t = H.t

  let create n = H.create n (entry V.default)
  let is_empty = H.is_empty
  let insert h v = H.insert h (entry v)
  let pop_min h = (H.pop_min h).value
end
