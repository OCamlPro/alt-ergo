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

(* Algorithm and constants from https://github.com/ztanml/fast-hash/ *)

type t = Int64.t

let[@inline] init seed =
  let h = Int64.logxor (Int64.of_int seed) 0x880355f21e6d1965L in
  h

let[@inline] mix h =
  let h = Int64.logxor h (Int64.shift_right_logical h 23) in
  let h = Int64.mul h 0x2127599bf4325c37L in
  let h = Int64.logxor h (Int64.shift_right_logical h 47) in
  h

let[@inline] combine_int n h =
  let h = Int64.logxor h (mix (Int64.of_int n)) in
  let h = Int64.mul h 0x880355f21e6d1965L in
  h

let[@inline] combine hash x h = combine_int (hash x) h

let[@inline] combine_list hash xs h =
  (* This is written with a [while] loop in order to make it easier for the
     compiler to unbox the [Int64]s involved. *)
  let h = ref h and xs = ref xs and len = ref 0 in
  while
    match !xs with
    | [] ->
      h := combine_int !len !h;
      false
    | x :: xs' ->
      h := combine_int (hash x) !h;
      xs := xs';
      incr len;
      true
  do
    ()
  done;
  !h

let[@inline] finalize h =
  let h = mix h in
  let h =
    (* Retain information from both lower and higher part of the hash on 32-bit
       platforms. *)
    if Sys.word_size < 64
    then Int64.sub h (Int64.shift_right_logical h 32)
    else h
  in
  Int64.to_int h
