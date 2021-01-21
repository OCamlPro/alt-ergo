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

[@@@ocaml.warning "-33"]
open Options

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
