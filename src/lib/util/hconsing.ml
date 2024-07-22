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
  let retain_list = ref []

  let next_id = ref 0

  let save_cache, reinit_cache =
    let saved_nid = ref 0 in
    let saved_retain_list = ref [] in
    let saved_storage = ref None in
    let save_cache () =
      saved_retain_list := !retain_list;
      saved_nid := !next_id;
      saved_storage := (
        let hw = HWeak.create Hashed.initial_size in
        HWeak.iter (HWeak.add hw) storage;
        Some hw
      )
    in
    let reinit_cache () =
      next_id := !saved_nid;
      retain_list := !saved_retain_list;
      HWeak.clear storage;
      match !saved_storage with
      | Some st -> HWeak.iter (HWeak.add storage) st
      | None -> ()
    in
    save_cache, reinit_cache

  let make d =
    let d = Hashed.set_id !next_id d in
    let o = HWeak.merge storage d in
    if o == d then begin
      incr next_id;
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
