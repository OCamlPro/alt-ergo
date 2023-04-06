(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

module type HASHED =
sig
  type elt
  val eq : elt -> elt -> bool
  val hash : elt -> int
  val set_id : int -> elt -> elt
  val initial_size : int
  val disable_weaks : unit -> bool
end

module type S =
sig
  type t
  val save_cache: unit -> unit
  val reinit_cache: unit -> unit
  val enable_gc_control : unit -> unit
  val make : t -> t
  val elements : unit -> t list
end

module Make(Hashed : HASHED) : (S with type t = Hashed.elt) =
struct
  type t = Hashed.elt

  module HWeak = Weak.Make
      (struct
        type t = Hashed.elt
        let equal = Hashed.eq
        let hash = Hashed.hash
      end)

  let storage = HWeak.create Hashed.initial_size

  module V : sig
    type 'a t

    val make : int -> 'a t

    val length : 'a t -> int

    val add : 'a t -> 'a -> bool

    val reset : 'a t -> unit

    val iter : 'a t -> ('a -> unit) -> unit

    val growth_hint : 'a t -> unit
  end = struct
    type 'a t = { mutable len: int ; mutable vals: 'a array }

    let make n = { len = 0 ; vals = Array.make n (Obj.magic 0) }

    let iter arr f =
      for i = 0 to arr.len - 1 do
        f arr.vals.(i)
      done

    let length { len; _ } = len

    let capacity { vals; _ } = Array.length vals

    let is_full arr = length arr = capacity arr

    let add arr v =
      if is_full arr then
        arr.vals <- Array.append arr.vals (make arr.len).vals;
      arr.vals.(arr.len) <- v;
      arr.len <- arr.len + 1;
      is_full arr

    let reset arr =
      let len = arr.len in
      arr.len <- 0;
      for i = 0 to len - 1 do
        arr.vals.(i) <- Obj.magic 0
      done

    let growth_hint arr =
      if 2 * arr.len > Array.length arr.vals then
        arr.vals <- Array.append arr.vals (make arr.len).vals
  end

  let retain = V.make 256

  let retain_list = ref []

  let next_id = ref 0

  let save_cache, reinit_cache =
    let saved_nid = ref 0 in
    let saved_retain_list = ref [] in
    let saved_storage = ref None in
    let saved_retain = ref None in
    let save_cache () =
      saved_retain_list := !retain_list;
      saved_nid := !next_id;
      saved_storage := (
        let hw = HWeak.create Hashed.initial_size in
        HWeak.iter (HWeak.add hw) storage;
        Some hw
      );
      saved_retain := (
        let saved_retain = V.make (V.length retain) in
        V.iter retain (fun e -> V.add saved_retain e |> ignore);
        Some saved_retain
      );
    in
    let reinit_cache () =
      next_id := !saved_nid;
      retain_list := !saved_retain_list;
      HWeak.clear storage;
      begin match !saved_storage with
      | Some st -> HWeak.iter (HWeak.add storage) st
      | None -> ()
      end;
      begin match !saved_retain with
      | Some sr -> V.iter sr (fun e -> V.add retain e |> ignore)
      | None -> ()
      end
    in
    save_cache, reinit_cache

  let gc_control = ref false

  let enable_gc_control () = gc_control := true

  let make d =
    let d = Hashed.set_id !next_id d in
    let o = HWeak.merge storage d in
    if o == d then begin
      incr next_id;
      if !gc_control && V.add retain d then begin
        Printer.print_dbg "!!! reset@.";
        V.reset retain;
        Gc.full_major ();
        HWeak.iter (fun e -> V.add retain e |> ignore) storage;
        V.growth_hint retain;
      end;
      if Hashed.disable_weaks() then
        (* retain a pointer to 'd' to prevent the GC from collecting
           the object if H.disable_weaks is set *)
        retain_list := d :: !retain_list
    end;
    o

  let elements () =
    let acc = ref [] in
    HWeak.iter (fun e -> acc := e :: !acc) storage;
    !acc

end
